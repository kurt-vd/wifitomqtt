/*
 * Copyright 2018 Kurt Van Dijck <dev.kurt@vandijck-laurijssen.be>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
#include <ctype.h>
#include <errno.h>
#include <math.h>
#include <signal.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <unistd.h>
#include <getopt.h>
#include <fcntl.h>
#include <locale.h>
#include <poll.h>
#include <syslog.h>
#include <sys/signalfd.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <mosquitto.h>
#ifdef NOPLAINPSK
#include <openssl/evp.h>
#endif

#include "libet/libt.h"
#include "common.h"

#define NAME "wifitomqtt"
#ifndef VERSION
#define VERSION "<undefined version>"
#endif

#define ESTR(num)	strerror(num)

/* program options */
static const char help_msg[] =
	NAME ": Control wpa-supplicant via MQTT\n"
	"usage:	" NAME " [OPTIONS ...] [FILE|DEVICE]\n"
	"\n"
	"Options\n"
	" -V, --version		Show version\n"
	" -v, --verbose		Be more verbose\n"
	"\n"
	" -h, --host=HOST[:PORT]Specify alternate MQTT host+port\n"
	" -i, --iface=IFACE	Control IFACE (default: wlan0)\n"
	" -S, --no-ap-bgscan	Emit empty bgscan for AP/Mesh networks\n"
	"			This avoids warnings on devices that cannot scan\n"
	"			while in AP/mesh mode\n"
	"\n"
	"Arguments\n"
	" FILE|DEVICE	Read input from FILE or DEVICE\n"
	;

#ifdef _GNU_SOURCE
static struct option long_opts[] = {
	{ "help", no_argument, NULL, '?', },
	{ "version", no_argument, NULL, 'V', },
	{ "verbose", no_argument, NULL, 'v', },

	{ "host", required_argument, NULL, 'h', },
	{ "iface", required_argument, NULL, 'i', },

	{ "no-ap-bgscan", no_argument, NULL, 'S', },
	{ },
};
#else
#define getopt_long(argc, argv, optstring, longopts, longindex) \
	getopt((argc), (argv), (optstring))
#endif
static const char optstring[] = "Vv?h:i:S";

/* signal handler */
static volatile int sigterm;
static volatile int ready;

/* logging */
static int loglevel = LOG_WARNING;

/* MQTT parameters */
static const char *mqtt_host = "localhost";
static int mqtt_port = 1883;
static int mqtt_keepalive = 10;
static int mqtt_qos = -1;

/* state */
static struct mosquitto *mosq;
static void publish_value(const char *value, const char *topic);
static void publish_ivalue_if_different(const char *newvalue, int *saved, const char *topic);
__attribute__((format(printf,1,2)))
static void publish_failure(const char *valuefmt, ...);
__attribute__((format(printf,1,2)))
static const char *valuetostr(const char *fmt, ...);
__attribute__((format(printf,1,2)))
static const char *topicfmt(const char *fmt, ...);

/* WPA */
static const char *iface = "wlan0";
static int wpasock;
static int have_bss_events;
static int wpa_lost;
static int curr_mode;
static char curr_bssid[20];
static int curr_level;
static int noapbgscan;
static int saved_rssi;
static int saved_speed;

static void myfree(void *dat)
{
	if (dat)
		free(dat);
}

/* WPA */
struct str {
	struct str *next;
	char a[1];
};

static struct str *strq, *strqlast;

static void add_strq(const char *a)
{
	struct str *str;

	str = malloc(sizeof(*str)+strlen(a));
	if (!str)
		mylog(LOG_ERR, "malloc str: %s", ESTR(errno));
	strcpy(str->a, a);

	/* linked list */
	if (strqlast)
		strqlast->next = str;
	else
		strq = str;
	strqlast = str;
	str->next = NULL;
}

static struct str *pop_strq(void)
{
	struct str *head;

	head = strq;
	if (head)
		strq = strq->next;
	if (!strq)
		strqlast = NULL;
	return head;
}

/* networks */
struct network {
	int id;
	char *ssid;
	int netflags;
#define NF_SEL	0x01
#define NF_REMOVE	0x02 /* remove requested before ADD_NETWORK completed */
	int flags;
	/* use BF_ flags */
	int mode; /* mode from config */
	int createseq;
	/* additional configurations to hold */
	char **cfgs;
	int ncfgs, scfgs;
};

/* incrementing counter to distinguish the order of network creation */
static int netcreateseq;

static struct network *networks;
static int nnetworks, snetworks;
static int last_ap_id = -1;
static int last_mesh_id = -1;

static int networkcmp(const void *a, const void *b)
{
	const struct network *na = a, *nb = b;

	return strcmp(na->ssid, nb->ssid);
}

static struct network *find_network_by_ssid(const char *ssid)
{
	struct network needle = {
		.ssid = (char *)ssid,
	};

	if (!ssid)
		return NULL;
	return bsearch(&needle, networks, nnetworks, sizeof(*networks), networkcmp);
}

static struct network *find_network_by_id(int idx)
{
	int j;

	for (j = 0; j < nnetworks; ++j)
		if (networks[j].id == idx)
			return networks+j;
	return NULL;
}

static struct network *add_network(int num, const char *ssid)
{
	struct network *net;

	if (nnetworks+1 > snetworks) {
		snetworks += 16;
		networks = realloc(networks, sizeof(*networks)*snetworks);
		if (!networks)
			mylog(LOG_ERR, "realloc %i networks: %s", snetworks, ESTR(errno));
	}
	net = &networks[nnetworks++];
	memset(net, 0, sizeof(*net));

	net->id = num;
	net->ssid = strdup(ssid);
	return net;
}

static void remove_network_configs(struct network *net);
static void remove_network(struct network *net)
{
	if (!net)
		return;
	/* handle memory */
	myfree(net->ssid);
	remove_network_configs(net);

	/* remove element, keep sorted */
	int idx = net - networks;
	if (idx != nnetworks-1)
		memmove(net, net+1, (nnetworks-1-idx)*sizeof(*networks));
	--nnetworks;
}

static inline void sort_networks(void)
{
	qsort(networks, nnetworks, sizeof(*networks), networkcmp);
}

struct bss {
	char bssid[20];
	char *ssid;
	int freq;
	int level;
	int flags;
		#define BF_WPA		0x01 /* 'w' */
		#define BF_WEP		0x02 /* 'W' */
		#define BF_EAP		0x04 /* 'e' */
		#define BF_KNOWN	0x08 /* 'k' */
		#define BF_DISABLED	0x10 /* 'd' */
		#define BF_PRESENT	0x40 /* for re-adding */
};

static struct bss *bsss;
static int nbsss, sbsss;

static const char *bssflagsstr(const struct bss *bss)
{
	static char buf[16];
	char *str;
	int mask;
	static const char indicators[] = "wWekd";
	const char *pind;

	str = buf;
	for (mask = 1, pind = indicators; *pind; ++pind, mask <<= 1)
		*str++ = (bss->flags & mask) ? *pind : '-';
	return buf;
}

static int bssidcmp(const void *a, const void *b)
{
	const struct bss *bssa = a, *bssb = b;

	return strcmp(bssa->bssid, bssb->bssid);
}

static struct bss *find_ap_by_bssid(const char *bssid)
{
	struct bss needle;

	if (!bssid)
		return NULL;

	strncpy(needle.bssid, bssid, sizeof(needle.bssid));
	return bsearch(&needle, bsss, nbsss, sizeof(*bsss), bssidcmp);
}

static void sort_ap(void)
{
	qsort(bsss, nbsss, sizeof(*bsss), bssidcmp);
}

static void compute_network_flags(struct bss *bss, const struct network *net)
{
	/* remove network related flags */
	bss->flags = bss->flags & ~(BF_KNOWN | BF_DISABLED);
	/* add network related flags */
	if (net)
		/* plain copy of the flags */
		bss->flags |= net->flags | BF_KNOWN;
}

static void compute_flags(struct bss *bss, const char *flags)
{
	bss->flags &= ~(BF_WPA | BF_WEP | BF_EAP);
	/* add BSS related flags */
	if (flags && strstr(flags, "WPA"))
		bss->flags |= BF_WPA;
	if (flags && strstr(flags, "WEP"))
		bss->flags |= BF_WEP;
	if (flags && strstr(flags, "EAP"))
		bss->flags |= BF_EAP;
}

static struct bss *add_ap(const char *bssid, int freq, int level, const char *ssid)
{
	struct bss *bss;

	if (nbsss+1 > sbsss) {
		sbsss += 16;
		bsss = realloc(bsss, sizeof(*bsss)*sbsss);
		if (!bsss)
			mylog(LOG_ERR, "realloc %i bsss: %s", sbsss, ESTR(errno));
	}
	bss = &bsss[nbsss++];
	memset(bss, 0, sizeof(*bss));
	strncpy(bss->bssid, bssid, sizeof(bss->bssid));
	bss->freq = freq;
	bss->level = level;
	if (ssid)
		bss->ssid = strdup(ssid);
	return bss;
}

static void remove_ap(struct bss *bss)
{
	if (!bss)
		return;
	/* handle memory */
	myfree(bss->ssid);

	/* remove element, remain sorted */
	int idx = bss - bsss;
	if (idx != nbsss-1)
		memcpy(bss, bss+1, (nbsss-1-idx)*sizeof(*bsss));
	--nbsss;
}

static void hide_ap_mqtt(const char *bssid)
{
	publish_value("", topicfmt("net/%s/bss/%s/freq", iface, bssid));
	publish_value("", topicfmt("net/%s/bss/%s/level", iface, bssid));
	publish_value("", topicfmt("net/%s/bss/%s/flags", iface, bssid));
	publish_value("", topicfmt("net/%s/bss/%s/ssid", iface, bssid));
}

/* aggregated state */
static const char *real_wifi_state;
static const char *pub_wifi_state;
static int selectedmode = -1; /* selected wpa_supplicant mode */
static int is_mode_off(void)
{
	struct network *net;
	int j;
	int nnet = 0, ndis = 0;

	/* find if all networks are disabled. Go off in that case */
	for (net = networks, j = 0; j < nnetworks; ++net, ++j) {
		if (selectedmode >= 0 && net->mode != selectedmode)
			continue;
		++nnet;
		if (net->flags & BF_DISABLED)
			++ndis;
	}
	return nnet && ndis >= nnet;
}
static void set_wifi_state(const char *str)
{
	real_wifi_state = str;
	if (!strcmp(str, "station")) {
		if (saved_speed)
			publish_value(NULL, topicfmt("net/%s/speed", iface));
		saved_speed = 0;
		if (saved_rssi)
			publish_value(NULL, topicfmt("net/%s/rssi", iface));
		saved_rssi = 0;
	}
	if (is_mode_off())
		/* publish mode 'off' if all is disabled */
		str = "off";

	if (!strcmp(str, pub_wifi_state ?: ""))
		return;
	mylog(LOG_INFO, "state %s => %s", pub_wifi_state ?: "", str);
	publish_value(str, topicfmt("net/%s/wifistate", iface));
	pub_wifi_state = str;
}
static inline void nets_enabled_changed(void)
{
	/* repeat wifi state, maybe some networks were enabled/disabled */
	set_wifi_state(real_wifi_state);
}


static int nstations;
static void set_wifi_stations(int n)
{
	char buf[16];

	nstations = n;
	sprintf(buf, "%i", n);
	if (n < 0)
		strcpy(buf, "");
	publish_value(buf, topicfmt("net/%s/stations", iface));
}

/* wpa functions */
static inline int mystrncmp(const char *needle, const char *haystack)
{
	return strncmp(needle, haystack, strlen(needle));
}

static void wpa_cmd_timeout(void *);
static void wpa_keepalive(void *);
__attribute__((format(printf,1,2)))
static int wpa_send(const char *fmt, ...)
{
	va_list va;
	char *line;
	int ret;

	va_start(va, fmt);
	vasprintf(&line, fmt, va);
	va_end(va);

	ret = send(wpasock, line, strlen(line), 0);
	if (ret < 0)
		mylog(LOG_ERR, "send wpa: %s", ESTR(errno));
	add_strq(line);
	mylog(LOG_DEBUG, "> %s", line);
	free(line);
	libt_add_timeout(3, wpa_cmd_timeout, NULL);
	libt_add_timeout(5, wpa_keepalive, NULL);
	return ret;
}

static void wpa_cmd_timeout(void *dat)
{
	/* no pong recvd, reattach? */
	mylog(LOG_WARNING, "wpa lost");
	wpa_lost = 1;
}

static void wpa_keepalive(void *dat)
{
	if (!curr_mode)
		wpa_send("SIGNAL_POLL");
	if (!curr_mode && curr_bssid[0])
		wpa_send("BSS %s", curr_bssid);
	else
		wpa_send("PING");
}

static struct network *find_last_network_mode(const struct network *exclude, int mode)
{
	struct network *net, *ap = NULL;

	for (net = networks; net < networks+nnetworks; ++net) {
		if (net == exclude)
			continue;
		if (net->mode == mode) {
			if (!ap || (net->id > ap->id))
				ap = net;
		}
	}
	return ap;
}

static void network_changed(const struct network *net, int removing)
{
	int j, flags;
	struct bss *bss;

	for (j = 0, bss = bsss; j < nbsss; ++j, ++bss) {
		if (!bss->ssid)
			continue;
		if (strcmp(bss->ssid, net->ssid))
			continue;
		flags = bss->flags;
		compute_network_flags(bss, removing ? NULL : net);
		if (flags != bss->flags)
			publish_value(bssflagsstr(bss), topicfmt("net/%s/bss/%s/flags", iface, bss->bssid));
	}

	/* keep track of 'lastAP' */
	struct network *lastap = find_last_network_mode(removing ? net : NULL, 2);
	int new_last_ap_id = lastap ? lastap->id : -1;

	if (new_last_ap_id != last_ap_id) {
		last_ap_id = new_last_ap_id;
		publish_value(lastap ? lastap->ssid : "", topicfmt("net/%s/lastAP", iface));
	}

	/* same for lastmesh */
	struct network *lastmesh = find_last_network_mode(removing ? net : NULL, 5);
	int new_last_mesh_id = lastmesh ? lastmesh->id : -1;

	if (new_last_mesh_id != last_mesh_id) {
		last_mesh_id = new_last_mesh_id;
		publish_value(lastmesh ? lastmesh->ssid : "", topicfmt("net/%s/lastmesh", iface));
	}
}

static void wpa_save_config(void)
{
	struct str *str;

	for (str = strq; str; str = str->next) {
		if (!mystrncmp("SET_NETWORK", str->a) ||
				!mystrncmp("ENABLE_NETWORK", str->a) ||
				!mystrncmp("DISABLE_NETWORK", str->a) ||
				!mystrncmp("SELECT_NETWORK", str->a) ||
				!mystrncmp("REMOVE_NETWORK", str->a) ||
				!mystrncmp("ADD_NETWORK", str->a))
			break;
	}
	if (!str)
		wpa_send("SAVE_CONFIG");
}

static void add_network_config(struct network *net, const char *key, const char *value)
{
#define CFGBLK	16

	if (net && net->id >= 0) {
		wpa_send("SET_NETWORK %i %s %s", net->id, key, value);
		return;
	}

	if (net->ncfgs+2 > net->scfgs) {
		net->scfgs = (net->ncfgs+2+CFGBLK-1) & ~(CFGBLK-1);
		net->cfgs = realloc(net->cfgs, sizeof(net->cfgs[0])*net->scfgs);
		if (!net->cfgs)
			mylog(LOG_ERR, "realloc %u cfgs: %s", net->scfgs, ESTR(errno));
	}
	net->cfgs[net->ncfgs++] = strdup(key);
	net->cfgs[net->ncfgs++] = strdup(value);
}

static void remove_network_configs(struct network *net)
{
	int j;

	for (j = 0; j < net->ncfgs; ++j)
		myfree(net->cfgs[j]);
	myfree(net->cfgs);
	net->ncfgs = 0;
	net->cfgs = NULL;
}

static void wpa_recvd_pkt(char *line)
{
	int ret, j;
	char *tok, *saveptr, *nl;
	struct str *head;

	ret = strlen(line);
	if (ret && line[ret-1] == '\n')
		line[ret-1] = 0;
	/* prepare log */
	nl = strchr(line, '\n');
	mylog(LOG_DEBUG, "< %.*s%s", (int)(nl ? nl - line : strlen(line)), line, nl ? " ..." : "");

	if (!mystrncmp("<2>", line) || !mystrncmp("<3>", line) || !mystrncmp("<4>", line)) {
		/* publish line+3 to mqtt log */
		char topic[128];

		/* don't use publish_value, it has hardcoded retain=1 */
		sprintf(topic, "tmp/%s/wpa", iface);
		ret = mosquitto_publish(mosq, NULL, topic, strlen(line+3), line+3, mqtt_qos, 0);
		if (ret)
			mylog(LOG_ERR, "mosquitto_publish %s: %s", topic, mosquitto_strerror(ret));
		/* process value */
		tok = strtok(line+3, " \t");
		if (!strcmp(tok, "CTRL-EVENT-CONNECTED")) {
			if (!curr_mode) {
				/* only set station when not connected as AP */
				set_wifi_state("station");
				wpa_send("SIGNAL_POLL");
			}
			wpa_send("STATUS");
		} else if (!strcmp(tok, "CTRL-EVENT-DISCONNECTED")) {
			wpa_send("STATUS");
			set_wifi_state("none");
		} else if (!strcmp(tok, "AP-ENABLED")) {
			curr_mode = 2;
			set_wifi_state("AP");
			set_wifi_stations(0);
		} else if (!strcmp(tok, "AP-DISABLED")) {
			curr_mode = 0;
			/* issue scan request immediately */
			wpa_send("SCAN");
			set_wifi_stations(-1);
		} else if (!strcmp(tok, "AP-STA-CONNECTED")) {
			set_wifi_stations(nstations+1);
		} else if (!strcmp(tok, "AP-STA-DISCONNECTED")) {
			set_wifi_stations(nstations-1);

		} else if (!strcmp(tok, "MESH-GROUP-STARTED")) {
			curr_mode = 5;
			set_wifi_state("mesh");
			set_wifi_stations(0);

		} else if (!strcmp(tok, "MESH-GROUP-REMOVED")) {
			curr_mode = 0;
			set_wifi_stations(-1);

		} else if (!strcmp(tok, "MESH-PEER-CONNECTED")) {
			set_wifi_stations(nstations+1);
		} else if (!strcmp(tok, "MESH-PEER-DISCONNECTED")) {
			set_wifi_stations(nstations-1);


		} else if (!strcmp(tok, "CTRL-EVENT-BSS-ADDED")) {
			strtok(NULL, " \t");
			tok = strtok(NULL, " \t");
			wpa_send("BSS %s", tok);
			have_bss_events = 1;
		} else if (!strcmp(tok, "CTRL-EVENT-BSS-REMOVED")) {
			strtok(NULL, " \t");
			tok = strtok(NULL, " \t");
			remove_ap(find_ap_by_bssid(tok));
			sort_ap();
			hide_ap_mqtt(tok);
			have_bss_events = 1;
		} else if (!strcmp(tok, "CTRL-EVENT-SCAN-RESULTS")) {
			if (!have_bss_events)
				wpa_send("SCAN_RESULTS");
		}
		return;
	}
	head = pop_strq();
	if (!head) {
		mylog(LOG_WARNING, "unsolicited response '%s'", line);
		return;
	}
	libt_remove_timeout(wpa_cmd_timeout, NULL);
	if (!strcmp(line, "FAIL") || !strcmp(line, "UNKNOWN COMMAND")) {
		if (!mystrncmp("STA-NEXT ", head->a) || !strcmp("STA-FIRST", head->a))
			/* AP station discovery fails on end-of-list */
			goto done;

		mylog(LOG_WARNING, "'%s': %.30s", head->a,  line);
		publish_failure("'%s': %.30s", strtok(head->a, " "), line);
	} else if (!*line) {
		mylog(LOG_INFO, "'%s': empty response", head->a);
		/* empty reply */
	} else if (!strcmp(head->a, "ATTACH")) {
		mylog(LOG_NOTICE, "wpa connected");

		wpa_send("LIST_NETWORKS");
		wpa_send("SCAN_RESULTS");
		wpa_send("STATUS");
		wpa_send("SCAN");

	} else if (!mystrncmp("GET_NETWORK ", head->a)) {
		int id;
		char *name;
		struct network *net;

		strtok(head->a, " "); /* pop GET_NETWORK */
		id = strtoul(strtok(NULL, " ") ?: "-1", NULL, 0);
		name = strtok(NULL, " ") ?: "";

		net = find_network_by_id(id);
		if (!net)
			goto done;

		if (!strcmp(name, "mode")) {
			net->mode = strtoul(line, NULL, 0);
			network_changed(net, 0);
		} else if (!strcmp(name, "disabled")) {
			if (strtoul(line, NULL, 0))
				net->flags |= BF_DISABLED;
			else
				net->flags &= ~BF_DISABLED;
			nets_enabled_changed();
			network_changed(net, 0);
		}

	} else if (!mystrncmp("SET_NETWORK ", head->a)) {
		int id;
		char *prop, *value;
		struct network *net;

		strtok(head->a, " "); /* pop SET_NETWORK */
		id = strtoul(strtok(NULL, " ") ?: "-1", NULL, 0);
		prop = strtok(NULL, " ") ?: "";
		value = strtok(NULL, " ") ?: "";

		net = find_network_by_id(id);
		if (!net)
			goto done;

		if (!strcmp(prop, "mode")) {
			net->mode = strtoul(value, NULL, 0);
			network_changed(net, 0);
		} else if (!strcmp(prop, "disabled")) {
			if (!strcmp(value, "1"))
				net->flags |= BF_DISABLED;
			else
				net->flags &= ~BF_DISABLED;
			nets_enabled_changed();
			network_changed(net, 0);
		}
		wpa_save_config();

	} else if (!strcmp("LIST_NETWORKS", head->a)) {
		/* clear network list */
		for (j = nnetworks; j > 0; --j)
			remove_network(networks+j);

		/* parse lines */
		int id;
		char *ssid;
		struct network *net;

		for (line = strtok_r(line, "\r\n", &saveptr); line;
				line = strtok_r(NULL, "\r\n", &saveptr)) {
			if (!mystrncmp("network id", line))
				/* header line */
				continue;
			id = strtoul(strtok(line, "\t"), NULL, 0);
			ssid = strtok(NULL, "\t");
			for (net = networks; net < networks+nnetworks; ++net) {
				if (!strcmp(ssid, net->ssid ?: "")) {
					/* remove duplicates */
					wpa_send("REMOVE_NETWORK %i", id);
					mylog(LOG_WARNING, "remove duplicate ssid '%s'", ssid);
					goto listitem_done;
				}
			}
			add_network(id, ssid);
			wpa_send("GET_NETWORK %i disabled", id);
			wpa_send("GET_NETWORK %i mode", id);
listitem_done:;
		}
		sort_networks();

	} else if (!strcmp(head->a, "SCAN_RESULTS")) {
		/* clear BF_PRESENT flag in bss list */
		for (j = 0; j < nbsss; ++j)
			bsss[j].flags &= ~BF_PRESENT;

		/* parse lines */
		char *bssid;
		struct bss *bss;
		for (line = strtok_r(line, "\r\n", &saveptr); line;
				line = strtok_r(NULL, "\r\n", &saveptr)) {
			if (!mystrncmp("bssid", line))
				/* header line */
				continue;
			bssid = strtok(line, "\t");
			/* process like 'hot-detected' bssid's */
			wpa_send("BSS %s", bssid);
			bss = find_ap_by_bssid(bssid);
			/* mark bss as present */
			if (bss)
				bss->flags |= BF_PRESENT;
		}
		for (j = 0; j < nbsss; ) {
			if (bsss[j].flags & BF_PRESENT) {
				++j;
				continue;
			}
			/* remove this bss */
			hide_ap_mqtt(bsss[j].bssid);
			remove_ap(bsss+j);
		}
		sort_ap();

	} else if (!mystrncmp("BSS ", head->a)) {
		char *bssid = NULL;
		char *ssid = NULL;
		char *flags = NULL;
		int freq = 0, level = 0;
		char *val;

		for (line = strtok_r(line, "\r\n", &saveptr); line;
				line = strtok_r(NULL, "\r\n", &saveptr)) {
			tok = strtok(line, "=");
			val = strtok(NULL, "=");

			if (!strcmp(tok, "bssid"))
				bssid = val;
			else if (!strcmp(tok, "freq"))
				freq = strtoul(val, NULL, 0);
			else if (!strcmp(tok, "level"))
				level = strtol(val, NULL, 0);
			else if (!strcmp(tok, "flags"))
				flags = val;
			else if (!strcmp(tok, "ssid"))
				ssid = val;
		}
		struct bss *bss;

		if (ssid && !strncmp(ssid, "\\x00", 4))
			/* ignore ssid's that start with \x00
			 * it's most probably a hidden ssid */
			goto done;

		bss = find_ap_by_bssid(bssid);
		if (bss) {
			if (bss->freq != freq)
				publish_value(valuetostr("%.3lfG", freq*1e-3),
						topicfmt("net/%s/bss/%s/freq", iface, bssid));
			if (bss->level != level)
				publish_value(valuetostr("%i", level),
						topicfmt("net/%s/bss/%s/level", iface, bssid));
			bss->freq = freq;
			bss->level = level;
			int savedflags = bss->flags;
			compute_flags(bss, flags);
			if (savedflags != bss->flags)
				publish_value(bssflagsstr(bss),
						topicfmt("net/%s/bss/%s/flags", iface, bssid));
		} else if (bssid) {
			struct bss *bss = add_ap(bssid, freq, level, ssid);

			publish_value(ssid, topicfmt("net/%s/bss/%s/ssid", iface, bssid));
			publish_value(valuetostr("%.3lfG", freq*1e-3),
					topicfmt("net/%s/bss/%s/freq", iface, bssid));
			publish_value(valuetostr("%i", level),
					topicfmt("net/%s/bss/%s/level", iface, bssid));
			/* publish flags as last */
			compute_flags(bss, flags);
			if (bss->ssid)
				compute_network_flags(bss, find_network_by_ssid(bss->ssid));
			publish_value(bssflagsstr(bss),
					topicfmt("net/%s/bss/%s/flags", iface, bssid));
			sort_ap();
		}
		/* publish corresponding level */
		if (!curr_mode && !strcmp(curr_bssid, bssid ?: "")) {
			if (level != curr_level)
				publish_value(valuetostr("%i", level),
						topicfmt("net/%s/level", iface));
			curr_level = level;
		}
	} else if (!strcmp("SIGNAL_POLL", head->a)) {
		char *val;

		for (line = strtok_r(line, "\r\n", &saveptr); line;
				line = strtok_r(NULL, "\r\n", &saveptr)) {
			tok = strtok(line, "=");
			val = strtok(NULL, "=");
			if (!strcasecmp(tok, "rssi"))
				publish_ivalue_if_different(val, &saved_rssi,
						topicfmt("net/%s/rssi", iface));

			else if (!strcasecmp(tok, "linkspeed"))
				publish_ivalue_if_different(val, &saved_speed,
						topicfmt("net/%s/speed", iface));
		}

	} else if (!strcmp("STATUS", head->a)) {
		char *val;
		char *ssid = NULL;
		char *mode = NULL;
		char *wpastate = NULL;
		int freq = 0;

		curr_bssid[0] = 0;
		for (line = strtok_r(line, "\r\n", &saveptr); line;
				line = strtok_r(NULL, "\r\n", &saveptr)) {
			tok = strtok(line, "=");
			val = strtok(NULL, "=");
			if (!strcmp(tok, "bssid"))
				strcpy(curr_bssid, val);
			else if (!strcmp(tok, "ssid"))
				ssid = val;
			else if (!strcmp(tok, "freq"))
				freq = strtoul(val, NULL, 0);
			else if (!strcmp(tok, "mode"))
				mode = val;
			else if (!strcmp(tok, "wpa_state"))
				wpastate = val;
		}
		if (!strcmp(curr_bssid, "00:00:00:00:00:00"))
			curr_bssid[0] = 0;

		if (!pub_wifi_state) {
			/* we just started, and this is the first iteration.
			 * Fix curr_mode and wifi_state
			 */
			if (!strcmp(mode ?: "", "AP"))
				curr_mode = 2;
			else if (!strcmp(mode ?: "", "mesh"))
				curr_mode = 5;

			if (curr_mode == 2) {
				set_wifi_state("AP");
				wpa_send("STA-FIRST");
				set_wifi_stations(0);
			} else if (curr_mode == 5) {
				set_wifi_state("mesh");
			} else if (!strcmp(wpastate ?: "", "COMPLETED") && !strcmp(mode ?: "", "station")) {
				set_wifi_state("station");
				publish_value("", topicfmt("net/%s/stations", iface));
			} else {
				set_wifi_state("none");
			}
		}

		publish_value(curr_bssid, topicfmt("net/%s/bssid", iface));
		if (freq && curr_mode) {
			publish_value(valuetostr("%.3lfG",freq*1e-3),
					topicfmt("net/%s/freq", iface));
			publish_value("", topicfmt("net/%s/level", iface));
			publish_value(ssid, topicfmt("net/%s/ssid", iface));
		} else if (freq && curr_bssid[0]) {
			publish_value(valuetostr("%.3lfG",freq*1e-3),
					topicfmt("net/%s/freq", iface));
			struct bss *bss = find_ap_by_bssid(curr_bssid);
			if (bss) {
				if (curr_level != bss->level)
					publish_value(valuetostr("%i", bss->level),
							topicfmt("net/%s/level", iface));
				curr_level = bss->level;
			}
			publish_value(ssid, topicfmt("net/%s/ssid", iface));
		} else {
			publish_value("", topicfmt("net/%s/freq", iface));
			publish_value("", topicfmt("net/%s/level", iface));
			publish_value("", topicfmt("net/%s/ssid", iface));
			curr_level = 0;
		}

	} else if (!strcmp("STA-FIRST", head->a)) {
		/* initial stations request */
		set_wifi_stations(1);
		wpa_send("STA-NEXT %s", strtok(line, "\r\n"));

	} else if (!strcmp("STA-NEXT", head->a)) {
		/* subsequent station request */
		set_wifi_stations(nstations+1);
		wpa_send("STA-NEXT %s", strtok(line, "\r\n"));

	} else if (!mystrncmp("ADD_NETWORK", head->a)) {
		struct network *net, *lp;
		int id, npending;

		id = strtoul(line, NULL, 0);
		/* find oldest id-less network */
		for (net = NULL, npending = 0, lp = networks; lp < networks+nnetworks; ++lp) {
			if (lp->id != -1)
				continue;
			++npending;
			if (!net || lp->createseq < net->createseq)
				net = lp;
		}
		if (npending <= 1)
			/* reset counter, and avoid potential overflows. */
			netcreateseq = 0;
		if (!net)
			goto done;
		net->id = id;
		if (net->netflags & NF_REMOVE) {
			wpa_send("REMOVE_NETWORK %i", id);
			network_changed(net, 1);
			remove_network(net);
			nets_enabled_changed();
			goto done;
		}

		wpa_send("SET_NETWORK %i ssid \"%s\"", id, net->ssid);
		for (j = 0; j < net->ncfgs; j += 2)
			wpa_send("SET_NETWORK %i %s %s", id, net->cfgs[j], net->cfgs[j+1]);
		remove_network_configs(net);

		if (net->netflags & NF_SEL)
			wpa_send("SELECT_NETWORK %i", id);
		else if (!(net->flags & BF_DISABLED))
			/* enable station-mode networks automatically */
			wpa_send("ENABLE_NETWORK %i", id);
		nets_enabled_changed();

	} else if (!mystrncmp("ENABLE_NETWORK all", head->a)) {
		for (j = 0; j < nnetworks; ++j) {
			if (networks[j].flags & BF_DISABLED) {
				networks[j].flags &= ~BF_DISABLED;
				network_changed(networks+j, 0);
			}
		}
		wpa_save_config();
		nets_enabled_changed();

	} else if (!mystrncmp("DISABLE_NETWORK all", head->a)) {
		for (j = 0; j < nnetworks; ++j) {
			if (!(networks[j].flags & BF_DISABLED)) {
				networks[j].flags |= BF_DISABLED;
				network_changed(networks+j, 0);
			}
		}
		wpa_save_config();
		nets_enabled_changed();

	} else if (!mystrncmp("ENABLE_NETWORK ", head->a)) {
		int idx = strtoul(head->a + 15, NULL, 0);
		struct network *net = find_network_by_id(idx);

		if (net) {// && (net->flags & BF_DISABLED)) {
			net->flags &= ~BF_DISABLED;
			network_changed(net, 0);
			wpa_save_config();
			nets_enabled_changed();
		}

	} else if (!mystrncmp("DISABLE_NETWORK ", head->a)) {
		int idx = strtoul(head->a + 16, NULL, 0);
		struct network *net = find_network_by_id(idx);

		if (net) {// && !(net->flags & BF_DISABLED)) {
			net->flags |= BF_DISABLED;
			network_changed(net, 0);
			wpa_save_config();
			nets_enabled_changed();
		}

	} else if (!mystrncmp("REMOVE_NETWORK ", head->a)) {
		wpa_save_config();

	} else if (!mystrncmp("SELECT_NETWORK ", head->a)) {
		int idx = strtoul(head->a + 15, NULL, 0);
		struct network *net;

		for (net = networks; net < networks+nnetworks; ++net) {
			if (net->id == idx)
				net->flags &= ~BF_DISABLED;
			else
				net->flags |= BF_DISABLED;
			network_changed(net, 0);
		}
		wpa_save_config();
		nets_enabled_changed();

	} else if (!strcmp("PING", head->a)) {
		/* ignore */
	} else if (!mystrncmp("SET ", head->a)) {
		wpa_save_config();

	} else {
		mylog(LOG_INFO, "'%.20s' OK", head->a);
	}
done:
	free(head);
}

static int wpa_connect(const char *iface)
{
	int ret, sock;
	struct sockaddr_un name = {
		.sun_family = AF_UNIX,
	};

	/* open client socket */
	ret = sock = socket(PF_UNIX, SOCK_DGRAM, 0);
	if (ret < 0)
		mylog(LOG_ERR, "socket unix: %s", ESTR(errno));
	/* connect to server */
	sprintf(name.sun_path, "/var/run/wpa_supplicant/%s", iface);
	ret = connect(sock, (struct sockaddr *)&name, SUN_LEN(&name));
	if (ret < 0)
		mylog(LOG_ERR, "connect %s: %s", name.sun_path, ESTR(errno));

	/* bind to abstract name */
	memset(name.sun_path, 0, sizeof(name.sun_path));
	sprintf(name.sun_path+1, "wpa-mqtt-%s-%i", iface, getpid());
	ret = bind(sock, (struct sockaddr *)&name, sizeof(name));
	if (ret < 0)
		mylog(LOG_ERR, "bind @%s: %s", name.sun_path+1, ESTR(errno));
	return sock;
}

/* MQTT API */
static struct network *find_or_create_ssid(const char *ssid)
{
	struct network *net;

	if (!ssid)
		return NULL;
	net = find_network_by_ssid(ssid);
	if (!net) {
		wpa_send("ADD_NETWORK");
		net = add_network(-1, ssid);
		net->createseq = ++netcreateseq;
		sort_networks();
		net = find_network_by_ssid(ssid);
	}
	return net;
}

static void my_mqtt_msg(struct mosquitto *mosq, void *dat, const struct mosquitto_message *msg)
{
	int ret;

	if (is_self_sync(msg))
		ready = 1;

	char **toks;
	int ntoks;

	ret = mosquitto_sub_topic_tokenise(msg->topic, &toks, &ntoks);
	if (ret)
		mylog(LOG_ERR, "mosquitto tokenize %s: %s", msg->topic, mosquitto_strerror(ret));
	if (ntoks >= 4 &&
			!strcmp(toks[0], "net") &&
			!strcmp(toks[1], iface) &&
			!strcmp(toks[2], "ssid")) {
		struct network *net;

		if (!strcmp(toks[3], "set")) {
			/* select new ssid. Do this only for new msgs (!retained) */
			if (!msg->payloadlen || !strcmp(msg->payload, "none")) {
				wpa_send("DISABLE_NETWORK all");
				selectedmode = -1;
			} else if (!strcmp(msg->payload, "all")) {
				wpa_send("ENABLE_NETWORK all");
				selectedmode = -1;
			} else {
				struct network *net;

				net = find_network_by_ssid(msg->payload ?: "");
				if (net && net->id >= 0)
					wpa_send("SELECT_NETWORK %i", net->id);
				else if (net)
					net->netflags |= NF_SEL;
				else
					mylog(LOG_INFO, "selected unknown network '%s'", (char *)msg->payload ?: "");
			}

		} else if (!strcmp(toks[3], "enable")) {
			net = find_network_by_ssid((char *)msg->payload);
			if (net && net->id >= 0)
				wpa_send("ENABLE_NETWORK %i", net->id);
			else if (net)
				/* queue flags already */
				net->flags &= ~BF_DISABLED;
			selectedmode = -1;

		} else if (!strcmp(toks[3], "disable")) {
			net = find_network_by_ssid((char *)msg->payload);
			if (net && net->id >= 0)
				wpa_send("DISABLE_NETWORK %i", net->id);
			else if (net)
				net->flags |= BF_DISABLED;
			selectedmode = -1;

		} else if (!strcmp(toks[3], "remove")) {
			net = find_network_by_ssid((char *)msg->payload);
			if (net && net->id >= 0) {
				wpa_send("REMOVE_NETWORK %i", net->id);
				network_changed(net, 1);
				remove_network(net);
				nets_enabled_changed();
			} else if (net)
				net->netflags |= NF_REMOVE;

		} else if (!strcmp(toks[3], "psk")) {
			/* ssid is first line of payload */
			char *ssid = strtok((char *)msg->payload, "\n\r=");
			/* psk is second line */
			char *psk = strtok(NULL, "\n\r");
#ifdef NOPLAINPSK
			/* test for plaintext PSK, and encrypt if so */
			if (*psk == '"' && psk[strlen(psk)-1] == '"') {
				/* strip " */
				psk[strlen(psk)-1] = 0;
				++psk;

				/* encrypt */
				static uint8_t binpsk[32];
				static char textpsk[65];
				if (!PKCS5_PBKDF2_HMAC_SHA1(psk, strlen(psk), (const void *)ssid, strlen(ssid),
						4096, sizeof(binpsk), binpsk)) {
					publish_failure("create psk for '%s' failed", ssid);
					goto psk_done;
				}
				/* convert to text */
				for (j =0; j < sizeof(binpsk); ++j)
					sprintf(textpsk[j*2], "%02x", binpsk[j]);
				psk = textpsk;
			}
#endif
			net = find_or_create_ssid(ssid);
			add_network_config(net, "psk", psk);
#ifdef NOPLAINPSK
/* add an empty statement after the label,
 * since C cannot label the end of a block.
 */
psk_done:;
#endif
		} else if (!strcmp(toks[3], "config") && ntoks == 5) {
			/* ssid is first line of payload */
			char *ssid = strtok((char *)msg->payload, "\n\r=");
			/* key is toks[4] */
			char *key = toks[4];

			/* value is second line */
			char *value = strtok(NULL, "\n\r");

			net = find_or_create_ssid(ssid);
			add_network_config(net, key, value);

		} else if (!strcmp(toks[3], "wep")) {
			/* TODO */
		} else if (!strcmp(toks[3], "ap")) {
			net = find_or_create_ssid((char *)msg->payload);

			/* AP-specific settings */
			add_network_config(net, "mode", "2");
			if (noapbgscan)
				add_network_config(net, "bgscan", "\"\"");
			net->mode = 2;
			if (net->id < 0)
				/* leave new AP network disabled */
				net->flags |= BF_DISABLED;

		} else if (!strcmp(toks[3], "mesh")) {
			net = find_or_create_ssid((char *)msg->payload);

			/* mesh-specific settings */
			add_network_config(net, "mode", "5");
			if (noapbgscan)
				add_network_config(net, "bgscan", "\"\"");
			net->mode = 5;
			if (net->id < 0) {
				/* set some defaults */
				add_network_config(net, "key_mgmt", "NONE");
				add_network_config(net, "frequency", "2437");
				/* leave new mesh network disabled */
				net->flags |= BF_DISABLED;
			}

		} else if (!strcmp(toks[3], "create")) {
			find_or_create_ssid((char *)msg->payload);
		}
	} else if (ntoks == 5 &&
			!strcmp(toks[0], "net") &&
			!strcmp(toks[1], iface) &&
			!strcmp(toks[2], "wifi") &&
			!strcmp(toks[3], "config")) {
		wpa_send("SET %s %s", toks[4], (char *)msg->payload);

	} else if (ntoks == 4 &&
			!strcmp(toks[0], "net") &&
			!strcmp(toks[1], iface) &&
			!strcmp(toks[2], "wifistate") &&
			!strcmp(toks[3], "set")) {
		if (!strcmp((char *)msg->payload, "off")) {
			wpa_send("DISABLE_NETWORK all");
			selectedmode = -1;

		} else if (!strcmp((char *)msg->payload, "any")) {
			wpa_send("ENABLE_NETWORK all");
			selectedmode = -1;

		} else {
			static const char *modes[] = {
				[0] = "station",
				[2] = "AP",
				[5] = "mesh",
			};
			selectedmode = -1;
			int j;

			for (j = 0; j < sizeof(modes)/sizeof(modes[0]); ++j) {
				if (modes[j] && !strcasecmp(modes[j], (char *)msg->payload)) {
					selectedmode = j;
					break;
				}
			}

			if (selectedmode != j) {
				mylog(LOG_INFO, "selected unknown wifi mode %s", (char *)msg->payload);
				goto wifimodeset_done;
			}

			mylog(LOG_INFO, "selected wifi mode %s (%i)", (char *)msg->payload, selectedmode);
			/* disable all networks, and enable those of the new mode */
			for (j = 0; j < nnetworks; ++j) {
				if (networks[j].id < 0) {
					if (networks[j].mode == selectedmode)
						networks[j].flags &= ~BF_DISABLED;
					else
						networks[j].flags |= BF_DISABLED;

				} else if (networks[j].mode == selectedmode && networks[j].flags & BF_DISABLED) {
					wpa_send("ENABLE_NETWORK %i", networks[j].id);

				} else if (networks[j].mode != selectedmode && !(networks[j].flags & BF_DISABLED)) {
					wpa_send("DISABLE_NETWORK %i", networks[j].id);
				}
			}
			/* clear current SSID, before ack of new wifistate */
			publish_value("", topicfmt("net/%s/ssid", iface));
			set_wifi_state(modes[selectedmode]);
		}
wifimodeset_done:
		;
	}
	mosquitto_sub_topic_tokens_free(&toks, ntoks);
}

static void publish_value(const char *value, const char *topic)
{
	int ret;

	/* publish cache */
	ret = mosquitto_publish(mosq, NULL, topic, strlen(value ?: ""), value, mqtt_qos, 1);
	if (ret)
		mylog(LOG_ERR, "mosquitto_publish %s: %s", topic, mosquitto_strerror(ret));
}

static void publish_ivalue_if_different(const char *newvalue, int *saved, const char *topic)
{
	int ret;
	int newivalue;

	newivalue = strtol(newvalue ?: "", NULL, 0);

	if (newivalue == *saved)
		return;

	newvalue = valuetostr("%i", newivalue);
	/* publish cache */
	ret = mosquitto_publish(mosq, NULL, topic, strlen(newvalue ?: ""), newvalue, mqtt_qos, 1);
	if (ret)
		mylog(LOG_ERR, "mosquitto_publish %s: %s", topic, mosquitto_strerror(ret));

	*saved = newivalue;
}

static void publish_failure(const char *valuefmt, ...)
{
	va_list va;
	int ret;
	static char topic[1024];
	static char value[1024];

	sprintf(topic, "net/%s/fail", iface);

	va_start(va, valuefmt);
	vsprintf(value, valuefmt, va);
	va_end(va);

	/* publish cache */
	ret = mosquitto_publish(mosq, NULL, topic, strlen(value), value, mqtt_qos, 0);
	if (ret)
		mylog(LOG_ERR, "mosquitto_publish %s: %s", topic, mosquitto_strerror(ret));
}

static const char *valuetostr(const char *fmt, ...)
{
	va_list va;
	static char value[128];

	va_start(va, fmt);
	vsprintf(value, fmt, va);
	va_end(va);

	return value;
}

static const char *topicfmt(const char *fmt, ...)
{
	va_list va;
	static char value[512];

	va_start(va, fmt);
	vsprintf(value, fmt, va);
	va_end(va);

	return value;
}

static void subscribe_topic(const char *topic)
{
	int ret;

	/* publish cache */
	ret = mosquitto_subscribe(mosq, NULL, topic, mqtt_qos);
	if (ret)
		mylog(LOG_ERR, "mosquitto_subscribe %s: %s", topic, mosquitto_strerror(ret));
}

static void do_mqtt_maintenance(void *dat)
{
	int ret;

	ret = mosquitto_loop_misc(mosq);
	if (ret)
		mylog(LOG_ERR, "mosquitto_loop_misc: %s", mosquitto_strerror(ret));
	libt_add_timeout(1, do_mqtt_maintenance, dat);
}

int main(int argc, char *argv[])
{
	int opt, ret, j;
	char *str;
	char mqtt_name[32];
	struct pollfd pf[3];

	setlocale(LC_ALL, "");
	/* argument parsing */
	while ((opt = getopt_long(argc, argv, optstring, long_opts, NULL)) >= 0)
	switch (opt) {
	case 'V':
		fprintf(stderr, "%s %s\nCompiled on %s %s\n",
				NAME, VERSION, __DATE__, __TIME__);
		exit(0);
	case 'v':
		++loglevel;
		break;
	case 'h':
		mqtt_host = optarg;
		str = strrchr(optarg, ':');
		if (str > mqtt_host && *(str-1) != ']') {
			/* TCP port provided */
			*str = 0;
			mqtt_port = strtoul(str+1, NULL, 10);
		}
		break;
	case 'i':
		iface = optarg;
		break;
	case 'S':
		noapbgscan = 1;
		break;

	default:
		fprintf(stderr, "unknown option '%c'", opt);
	case '?':
		fputs(help_msg, stderr);
		exit(1);
		break;
	}

	setmylog(NAME, 0, LOG_LOCAL2, loglevel);

	/* WPA */
	wpasock = wpa_connect(iface);
	wpa_send("ATTACH");
	/* MQTT start */
	if (mqtt_qos < 0)
		mqtt_qos = !strcmp(mqtt_host ?: "", "localhost") ? 0 : 1;
	mosquitto_lib_init();
	sprintf(mqtt_name, "%s-%i", NAME, getpid());
	mosq = mosquitto_new(mqtt_name, true, NULL);
	if (!mosq)
		mylog(LOG_ERR, "mosquitto_new failed: %s", ESTR(errno));
	/* mosquitto_will_set(mosq, "TOPIC", 0, NULL, mqtt_qos, 1); */

	ret = mosquitto_connect(mosq, mqtt_host, mqtt_port, mqtt_keepalive);
	if (ret)
		mylog(LOG_ERR, "mosquitto_connect %s:%i: %s", mqtt_host, mqtt_port, mosquitto_strerror(ret));
	mosquitto_message_callback_set(mosq, my_mqtt_msg);
	subscribe_topic(topicfmt("net/%s/ssid/+", iface));
	subscribe_topic(topicfmt("net/%s/wifistate/set", iface));

	libt_add_timeout(0, do_mqtt_maintenance, mosq);

	/* prepare signalfd */
	struct signalfd_siginfo sfdi;
	sigset_t sigmask;
	int sigfd;

	sigemptyset(&sigmask);
	sigfillset(&sigmask);

	if (sigprocmask(SIG_BLOCK, &sigmask, NULL) < 0)
		mylog(LOG_ERR, "sigprocmask: %s", ESTR(errno));
	sigfd = signalfd(-1, &sigmask, SFD_NONBLOCK | SFD_CLOEXEC);
	if (sigfd < 0)
		mylog(LOG_ERR, "signalfd failed: %s", ESTR(errno));
	/* prepare poll */
	pf[0].fd = wpasock;
	pf[0].events = POLL_IN;
	pf[1].fd = mosquitto_socket(mosq);
	pf[1].events = POLL_IN;
	pf[2].fd = sigfd;
	pf[2].events = POLL_IN;

	for (;;) {
		libt_flush();
		if (wpa_lost)
			break;
		if (mosquitto_want_write(mosq)) {
			ret = mosquitto_loop_write(mosq, 1);
			if (ret)
				mylog(LOG_WARNING, "mosquitto_loop_write: %s", mosquitto_strerror(ret));
		}
		ret = poll(pf, 3, libt_get_waittime());
		if (ret < 0 && errno == EINTR)
			continue;
		if (ret < 0)
			mylog(LOG_ERR, "poll ...");
		if (pf[0].revents) {
			static char line[1024*16];
			/* read input events */
			ret = recv(wpasock, line, sizeof(line)-1, 0);
			if (ret < 0 && errno == EINTR)
				continue;
			if (ret < 0) {
				mylog(LOG_WARNING, "recv wpa: %s", ESTR(errno));
				break;
			}
			line[ret] = 0;
			wpa_recvd_pkt(line);
		}
		if (pf[1].revents) {
			/* mqtt read ... */
			ret = mosquitto_loop_read(mosq, 1);
			if (ret) {
				mylog(LOG_WARNING, "mosquitto_loop_read: %s", mosquitto_strerror(ret));
				if (ret == MOSQ_ERR_CONN_LOST)
					/* no use to try to publish more */
					exit(1);
				break;
			}
		}
		while (pf[2].revents) {
			ret = read(sigfd, &sfdi, sizeof(sfdi));
			if (ret < 0 && errno == EAGAIN)
				break;
			if (ret < 0)
				mylog(LOG_ERR, "read signalfd: %s", ESTR(errno));
			switch (sfdi.ssi_signo) {
			case SIGTERM:
			case SIGINT:
				goto done;
				break;
			}
		}
	}
done:

	/* clean scan results in mqtt */
	for (j = 0; j < nbsss; ++j) {
		publish_value("", topicfmt("net/%s/bss/%s/freq", iface, bsss[j].bssid));
		publish_value("", topicfmt("net/%s/bss/%s/level", iface, bsss[j].bssid));
		publish_value("", topicfmt("net/%s/bss/%s/ssid", iface, bsss[j].bssid));
		publish_value("", topicfmt("net/%s/bss/%s/flags", iface, bsss[j].bssid));
	}
	publish_value("", topicfmt("net/%s/speed", iface));
	publish_value("", topicfmt("net/%s/rssi", iface));
	publish_value("", topicfmt("net/%s/bssid", iface));
	publish_value("", topicfmt("net/%s/freq", iface));
	publish_value("", topicfmt("net/%s/level", iface));
	publish_value("", topicfmt("net/%s/ssid", iface));
	publish_value("", topicfmt("net/%s/lastAP", iface));
	publish_value("", topicfmt("net/%s/lastmesh", iface));
	publish_value("", topicfmt("net/%s/stations", iface));
	publish_value("", topicfmt("net/%s/wifistate", iface));

	/* terminate */
	send_self_sync(mosq, mqtt_qos);
	while (!ready) {
		ret = mosquitto_loop(mosq, 10, 1);
		if (ret)
			mylog(LOG_ERR, "mosquitto_loop: %s", mosquitto_strerror(ret));
	}

#if 0
	/* free memory */
	for (j = 0; j < nbsss; ++j)
		myfree(bsss[j].ssid);
	myfree(bsss);
	for (j = 0; j < nnetworks; ++j) {
		myfree(networks[j].ssid);
		remove_network_configs(&networks[j]);
	}
	myfree(networks);

	struct str *head;
	for (head = pop_strq(); head; head = pop_strq())
		free(head);

	mosquitto_disconnect(mosq);
	mosquitto_destroy(mosq);
	mosquitto_lib_cleanup();
#endif
	return !sigterm;
}
