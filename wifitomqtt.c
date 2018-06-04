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
#include <sys/socket.h>
#include <sys/un.h>
#include <mosquitto.h>

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

	{ },
};
#else
#define getopt_long(argc, argv, optstring, longopts, longindex) \
	getopt((argc), (argv), (optstring))
#endif
static const char optstring[] = "Vv?h:i:";

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
__attribute__((format(printf,2,3)))
static void publish_value(const char *value, const char *topicfmt, ...);
__attribute__((format(printf,1,2)))
static const char *valuetostr(const char *fmt, ...);

/* WPA */
static const char *iface = "wlan0";
static int wpasock;
static int have_bss_events;
static int wpa_lost;
static int self_ap; /* we are AP ourselve */
static char curr_bssid[20];
static int curr_level;

/* signalling */
static int mysignal(int signr, void (*fn)(int))
{
	struct sigaction sa = {
		.sa_handler = fn,
	};
	return sigaction(signr, &sa, NULL);
}
static void onsigterm(int signr)
{
	sigterm = 1;
}

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
	char *psk;
	int netflags;
#define NF_SEL	0x01
	int flags;
	/* use BF_ flags */
};

static struct network *networks;
static int nnetworks, snetworks;
static int last_ap_id = -1;

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

static void remove_network(struct network *net)
{
	if (!net)
		return;
	/* handle memory */
	myfree(net->ssid);
	myfree(net->psk);

	/* remove element, keep sorted */
	int idx = net - networks;
	if (idx != nnetworks-1)
		memcpy(networks, networks+1, (nnetworks-1-idx)*sizeof(*networks));
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
		#define BF_AP		0x20 /* 'a' is accesspoint mode */
		#define BF_PRESENT	0x40 /* for re-adding */
};

static struct bss *bsss;
static int nbsss, sbsss;

static const char *bssflagsstr(const struct bss *bss)
{
	static char buf[16];
	char *str;
	int mask;
	static const char indicators[] = "wWekda";
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
	bss->flags = bss->flags & ~(BF_AP | BF_KNOWN | BF_DISABLED);
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
	publish_value("", "net/%s/bss/%s/freq", iface, bssid);
	publish_value("", "net/%s/bss/%s/level", iface, bssid);
	publish_value("", "net/%s/bss/%s/flags", iface, bssid);
	publish_value("", "net/%s/bss/%s/ssid", iface, bssid);
}

/* aggregated state */
static const char *wifi_state;
static void set_wifi_state(const char *str)
{
	if (!strcmp(str, wifi_state ?: ""))
		return;
	mylog(LOG_INFO, "state %s => %s", wifi_state ?: "", str);
	wifi_state = str;

	publish_value(wifi_state, "net/%s/wifistate", iface);
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
	libt_add_timeout(0.5, wpa_cmd_timeout, NULL);
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
	/*
	if (!self_ap && curr_bssid[0])
		wpa_send("BSS %s", curr_bssid);
	else
	*/
		wpa_send("PING");
}

static struct network *find_last_apcfg(const struct network *exclude)
{
	struct network *net, *ap = NULL;

	for (net = networks; net < networks+nnetworks; ++net) {
		if (net == exclude)
			continue;
		if (net->flags & BF_AP) {
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
		if (strcmp(bss->ssid, net->ssid))
			continue;
		flags = bss->flags;
		compute_network_flags(bss, removing ? NULL : net);
		if (flags != bss->flags)
			publish_value(bssflagsstr(bss), "net/%s/bss/%s/flags", iface, bss->bssid);
	}

	/* keep track of 'lastAP' */
	struct network *lastap = find_last_apcfg(removing ? net : NULL);
	int new_last_ap_id = lastap ? lastap->id : -1;

	if (new_last_ap_id != last_ap_id) {
		last_ap_id = new_last_ap_id;
		publish_value(lastap ? lastap->ssid : "", "net/%s/lastAP", iface);
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

static void wpa_recvd_pkt(char *line)
{
	int ret, j;
	char *tok, *saveptr, *nl;
	struct str *head;

	ret = strlen(line);
	line[ret] = 0;
	if (ret && line[ret-1] == '\n')
		line[ret-1] = 0;
	/* prepare log */
	nl = strchr(line, '\n');
	mylog(LOG_DEBUG, "< %.*s%s", (int)(nl ? nl - line : strlen(line)), line, nl ? " ..." : "");

	if (!mystrncmp("<2>", line) || !mystrncmp("<3>", line) || !mystrncmp("<4>", line)) {
		/* publish line+3 to mqtt log */
		publish_value(line+3, "tmp/%s/wpa", iface);
		tok = strtok(line+3, " \t");
		if (!strcmp(tok, "CTRL-EVENT-CONNECTED")) {
			if (!self_ap)
				/* only set station when not connected as AP */
				set_wifi_state("station");
			wpa_send("STATUS");
		} else if (!strcmp(tok, "CTRL-EVENT-DISCONNECTED")) {
			wpa_send("STATUS");
			set_wifi_state("none");
		} else if (!strcmp(tok, "AP-ENABLED")) {
			self_ap = 1;
			set_wifi_state("AP");
		} else if (!strcmp(tok, "AP-DISABLED")) {
			self_ap = 0;
			/* issue scan request immediately */
			wpa_send("SCAN");
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
		mylog(LOG_WARNING, "'%s': %.30s", head->a,  line);
	} else if (!*line) {
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
		int flags = net->flags;

		if (!strcmp(name, "mode")) {
			if (strtoul(line, NULL, 0) == 2)
				net->flags |= BF_AP;
			else
				net->flags &= ~BF_AP;
		} else if (!strcmp(name, "disabled")) {
			if (strtoul(line, NULL, 0))
				net->flags |= BF_DISABLED;
			else
				net->flags &= ~BF_DISABLED;
		}
		if (flags != net->flags)
			network_changed(net, 0);

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
			if (!strcmp(value, "2"))
				net->flags |= BF_AP;
			else
				net->flags &= ~BF_AP;
		} else if (!strcmp(prop, "disabled")) {
			if (!strcmp(value, "1"))
				net->flags |= BF_DISABLED;
			else
				net->flags &= ~BF_DISABLED;
		}
		network_changed(net, 0);

	} else if (!strcmp("LIST_NETWORKS", head->a)) {
		/* clear network list */
		for (j = nnetworks; j > 0; --j)
			remove_network(networks+j);

		/* parse lines */
		int id;
		char *ssid;
		for (line = strtok_r(line, "\r\n", &saveptr); line;
				line = strtok_r(NULL, "\r\n", &saveptr)) {
			if (!mystrncmp("network id", line))
				/* header line */
				continue;
			id = strtoul(strtok(line, "\t"), NULL, 0);
			ssid = strtok(NULL, "\t");
			add_network(id, ssid);
			wpa_send("GET_NETWORK %i mode", id);
			wpa_send("GET_NETWORK %i disabled", id);
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

		bss = find_ap_by_bssid(bssid);
		if (bss) {
			if (bss->freq != freq)
				publish_value(valuetostr("%.3lfG", freq*1e-3), "net/%s/bss/%s/freq", iface, bssid);
			if (bss->level != level)
				publish_value(valuetostr("%i", level), "net/%s/bss/%s/level", iface, bssid);
			bss->freq = freq;
			bss->level = level;
			if (!self_ap && !strcmp(curr_bssid, bssid ?: "")) {
				if (level != curr_level)
					publish_value(valuetostr("%i", level), "net/%s/level", iface);
				curr_level = level;
			}
			int savedflags = bss->flags;
			compute_flags(bss, flags);
			if (savedflags != bss->flags)
				publish_value(bssflagsstr(bss), "net/%s/bss/%s/flags", iface, bssid);
		} else if (bssid) {
			struct bss *bss = add_ap(bssid, freq, level, ssid);

			publish_value(ssid, "net/%s/bss/%s/ssid", iface, bssid);
			publish_value(valuetostr("%.3lfG", freq*1e-3), "net/%s/bss/%s/freq", iface, bssid);
			publish_value(valuetostr("%i", level), "net/%s/bss/%s/level", iface, bssid);
			/* publish flags as last */
			compute_flags(bss, flags);
			compute_network_flags(bss, find_network_by_ssid(bss->ssid));
			publish_value(bssflagsstr(bss), "net/%s/bss/%s/flags", iface, bssid);
			sort_ap();
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
				self_ap = !strcmp(val, "AP");
		}

		if (!wifi_state) {
			/* we just started, and this is the first iteration.
			 * Fix self_ap and wifi_state
			 */
			self_ap = !strcmp(mode ?: "", "AP");
			if (self_ap)
				set_wifi_state("AP");
			else if (!strcmp(wpastate ?: "", "COMPLETED") && !strcmp(mode ?: "", "station"))
				set_wifi_state("station");
		}

		publish_value(curr_bssid, "net/%s/bssid", iface);
		if (freq && self_ap) {
			publish_value(valuetostr("%.3lfG",freq*1e-3), "net/%s/freq", iface);
			publish_value("", "net/%s/level", iface);
			publish_value(ssid, "net/%s/ssid", iface);
		} else if (freq && curr_bssid[0]) {
			publish_value(valuetostr("%.3lfG",freq*1e-3), "net/%s/freq", iface);
			struct bss *bss = find_ap_by_bssid(curr_bssid);
			if (bss) {
				if (curr_level != bss->level)
					publish_value(valuetostr("%i", bss->level), "net/%s/level", iface);
				curr_level = bss->level;
			}
			publish_value(ssid, "net/%s/ssid", iface);
		} else {
			publish_value("", "net/%s/freq", iface);
			publish_value("", "net/%s/level", iface);
			publish_value("", "net/%s/ssid", iface);
			curr_level = 0;
		}

	} else if (!mystrncmp("ADD_NETWORK", head->a)) {
		struct network *net;
		int id;

		id = strtoul(line, NULL, 0);
		/* find first id-less network */
		net = find_network_by_id(-1);
		if (!net)
			goto done;
		net->id = id;
		wpa_send("SET_NETWORK %i ssid \"%s\"", id, net->ssid);
		if (net->psk) {
			wpa_send("SET_NETWORK %i psk %s", id, net->psk);
			free(net->psk);
			net->psk = NULL;
		}
		if (net->flags & BF_AP)
			wpa_send("SET_NETWORK %i mode 2", id);

		if (net->netflags & NF_SEL)
			wpa_send("SELECT_NETWORK %i", id);
		else if (!(net->flags & BF_AP))
			/* enable station-mode networks automatically */
			wpa_send("ENABLE_NETWORK %i", id);

	} else if (!mystrncmp("ENABLE_NETWORK all", head->a)) {
		for (j = 0; j < nnetworks; ++j) {
			if (networks[j].flags & BF_DISABLED) {
				networks[j].flags &= ~BF_DISABLED;
				network_changed(networks+j, 0);
			}
		}
		wpa_save_config();

	} else if (!mystrncmp("ENABLE_NETWORK ", head->a)) {
		int idx = strtoul(head->a + 15, NULL, 0);
		struct network *net = find_network_by_id(idx);

		if (net) {// && (net->flags & BF_DISABLED)) {
			net->flags &= ~BF_DISABLED;
			network_changed(net, 0);
			wpa_save_config();
		}

	} else if (!mystrncmp("DISABLE_NETWORK ", head->a)) {
		int idx = strtoul(head->a + 16, NULL, 0);
		struct network *net = find_network_by_id(idx);

		if (net) {// && !(net->flags & BF_DISABLED)) {
			net->flags |= BF_DISABLED;
			network_changed(net, 0);
			wpa_save_config();
		}

	} else if (!mystrncmp("REMOVE_NETWORK ", head->a)) {
		int idx = strtoul(head->a + 15, NULL, 0);
		struct network *net = find_network_by_id(idx);

		if (net) {
			network_changed(net, 1);
			wpa_save_config();
			remove_network(net);
		}

	} else if (!mystrncmp("SET_NETWORK ", head->a)) {
		wpa_save_config();

	} else if (!mystrncmp("SELECT_NETWORK ", head->a)) {
		wpa_save_config();

	} else if (!strcmp("PING", head->a)) {
		/* ignore */
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
	if (ret < 0)
		mylog(LOG_ERR, "mosquitto tokenize %s: %s", msg->topic, mosquitto_strerror(ret));
	if (ntoks >= 4 &&
			!strcmp(toks[0], "net") &&
			!strcmp(toks[1], iface) &&
			!strcmp(toks[2], "ssid")) {
		struct network *net;

		if (!strcmp(toks[3], "set")) {
			/* select new ssid. Do this only for new msgs (!retained) */
			if (msg->payloadlen && strcmp(msg->payload, "all")) {
				struct network *net;

				net = find_network_by_ssid(msg->payload ?: "");
				if (net && net->id > 0)
					wpa_send("SELECT_NETWORK %i", net->id);
				else if (net)
					net->netflags |= NF_SEL;
				else
					mylog(LOG_INFO, "selected unknown network '%s'", (char *)msg->payload ?: "");
			} else
				wpa_send("ENABLE_NETWORK all");

		} else if (!strcmp(toks[3], "enable")) {
			net = find_network_by_ssid((char *)msg->payload);

			if (net) {
				net->flags &= ~BF_DISABLED;
				wpa_send("ENABLE_NETWORK %i", net->id);
			}

		} else if (!strcmp(toks[3], "disable")) {
			net = find_network_by_ssid((char *)msg->payload);

			if (net) {
				net->flags |= BF_DISABLED;
				wpa_send("DISABLE_NETWORK %i", net->id);
			}

		} else if (!strcmp(toks[3], "remove")) {
			net = find_network_by_ssid((char *)msg->payload);

			if (net) {
				net->flags &= BF_KNOWN;
				wpa_send("REMOVE_NETWORK %i", net->id);
			}
		} else if (!strcmp(toks[3], "psk")) {
			/* ssid is first line of payload */
			net = find_or_create_ssid(strtok((char *)msg->payload, "\n\r"));
			if (!net)
				goto done;

			char *psk = strtok(NULL, "\n\r");
			if (net->id >= 0)
				wpa_send("SET_NETWORK %i psk %s", net->id, psk);
			else {
				myfree(net->psk);
				net->psk = strdup(psk);
			}
		} else if (!strcmp(toks[3], "wep")) {
			/* TODO */
		} else if (!strcmp(toks[3], "ap")) {
			net = find_or_create_ssid((char *)msg->payload);
			if (!net)
				goto done;
			net->flags |= BF_AP;
			if (net->id >= 0)
				wpa_send("SET_NETWORK %i mode %i", net->id, (net->flags & BF_AP) ? 2 : 0);

		} else if (!strcmp(toks[3], "create")) {
			find_or_create_ssid((char *)msg->payload);
		}
	}
done:
	mosquitto_sub_topic_tokens_free(&toks, ntoks);
}

static void publish_value(const char *value, const char *topicfmt, ...)
{
	va_list va;
	int ret;
	static char topic[1024];

	va_start(va, topicfmt);
	vsprintf(topic, topicfmt, va);
	va_end(va);

	/* publish cache */
	ret = mosquitto_publish(mosq, NULL, topic, strlen(value ?: ""), value, mqtt_qos, 1);
	if (ret < 0)
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

static void subscribe_topic(const char *topicfmt, ...)
{
	va_list va;
	int ret;
	char *topic;

	va_start(va, topicfmt);
	vasprintf(&topic, topicfmt, va);
	va_end(va);

	/* publish cache */
	ret = mosquitto_subscribe(mosq, NULL, topic, mqtt_qos);
	if (ret < 0)
		mylog(LOG_ERR, "mosquitto_subscribe %s: %s", topic, mosquitto_strerror(ret));
	free(topic);
}


int main(int argc, char *argv[])
{
	int opt, ret, j;
	char *str;
	char mqtt_name[32];
	struct pollfd pf[2];

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

	default:
		fprintf(stderr, "unknown option '%c'", opt);
	case '?':
		fputs(help_msg, stderr);
		exit(1);
		break;
	}

	setmylog(NAME, 0, LOG_LOCAL2, loglevel);
	mysignal(SIGINT, onsigterm);
	mysignal(SIGTERM, onsigterm);

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
	subscribe_topic("net/%s/ssid/+", iface);

	/* prepare poll */
	pf[0].fd = wpasock;
	pf[0].events = POLL_IN;
	pf[1].fd = mosquitto_socket(mosq);
	pf[1].events = POLL_IN;

	while (!sigterm) {
		libt_flush();
		if (wpa_lost)
			break;
		ret = poll(pf, 2, libt_get_waittime());
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
			if (!ret) {
				mylog(LOG_WARNING, "wpa closed");
				//break;
			}
			line[ret] = 0;
			wpa_recvd_pkt(line);
		}
		if (pf[1].revents) {
			/* mqtt read ... */
			ret = mosquitto_loop_read(mosq, 1);
			if (ret) {
				mylog(LOG_WARNING, "mosquitto_loop_read: %s", mosquitto_strerror(ret));
				break;
			}
		}
		/* mosquitto things to do each iteration */
		ret = mosquitto_loop_misc(mosq);
		if (ret) {
			mylog(LOG_WARNING, "mosquitto_loop_misc: %s", mosquitto_strerror(ret));
			break;
		}
		if (mosquitto_want_write(mosq)) {
			ret = mosquitto_loop_write(mosq, 1);
			if (ret) {
				mylog(LOG_WARNING, "mosquitto_loop_write: %s", mosquitto_strerror(ret));
			}
		}
	}

	/* clean scan results in mqtt */
	for (j = 0; j < nbsss; ++j) {
		publish_value("", "net/%s/bss/%s/freq", iface, bsss[j].bssid);
		publish_value("", "net/%s/bss/%s/level", iface, bsss[j].bssid);
		publish_value("", "net/%s/bss/%s/ssid", iface, bsss[j].bssid);
		publish_value("", "net/%s/bss/%s/flags", iface, bsss[j].bssid);
	}
	publish_value("", "net/%s/bssid", iface);
	publish_value("", "net/%s/freq", iface);
	publish_value("", "net/%s/level", iface);
	publish_value("", "net/%s/ssid", iface);
	publish_value("", "net/%s/lastAP", iface);

	/* terminate */
	send_self_sync(mosq, mqtt_qos);
	while (!ready) {
		ret = mosquitto_loop(mosq, 10, 1);
		if (ret < 0)
			mylog(LOG_ERR, "mosquitto_loop: %s", mosquitto_strerror(ret));
	}

#if 0
	/* free memory */
	for (j = 0; j < nbsss; ++j)
		myfree(bsss[j].ssid);
	myfree(bsss);
	for (j = 0; j < nnetworks; ++j) {
		myfree(networks[j].ssid);
		myfree(networks[j].psk);
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
