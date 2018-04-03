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
};

static struct network *networks;
static int nnetworks, snetworks;
static struct network *newnetwork;

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

	return bsearch(&needle, networks, nnetworks, sizeof(*networks), networkcmp);
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

static inline void sort_networks(void)
{
	qsort(networks, nnetworks, sizeof(*networks), networkcmp);
}

struct ap {
	char bssid[20];
	char *ssid;
	int freq;
	int level;
	int flags;
		#define BF_WPA		0x01
		#define BF_KNOWN	0x02
		#define BF_PRESENT	0x04 /* for re-adding */
};

static struct ap *aps;
static int naps, saps;

static int apbssidcmp(const void *a, const void *b)
{
	const struct ap *aap = a, *bap = b;

	return strcmp(aap->bssid, bap->bssid);
}

static struct ap *find_ap_by_bssid(const char *bssid)
{
	struct ap needle;

	if (!bssid)
		return NULL;

	strncpy(needle.bssid, bssid, sizeof(needle.bssid));
	return bsearch(&needle, aps, naps, sizeof(*aps), apbssidcmp);
}

static void add_ap(const char *bssid, int freq, int level, const char *flags, const char *ssid)
{
	struct ap *ap;

	if (naps+1 > saps) {
		saps += 16;
		aps = realloc(aps, sizeof(*aps)*saps);
		if (!aps)
			mylog(LOG_ERR, "realloc %i aps: %s", saps, ESTR(errno));
	}
	ap = &aps[naps++];
	memset(ap, 0, sizeof(*ap));
	strncpy(ap->bssid, bssid, sizeof(ap->bssid));
	ap->freq = freq;
	ap->level = level;
	/* TODO: flags */
	if (ssid) {
		ap->ssid = strdup(ssid);
		if (find_network_by_ssid(ssid))
			ap->flags |= BF_KNOWN;
	}
	qsort(aps, naps, sizeof(*aps), apbssidcmp);
}

static void remove_ap(struct ap *ap)
{
	if (!ap)
		return;
	/* handle memory */
	myfree(ap->ssid);

	/* remove element */
	int idx = ap - aps;
	if (idx != naps-1)
		memcpy(ap, ap+1, (naps-1-idx)*sizeof(*aps));
	--naps;
}

static void hide_ap_mqtt(const char *bssid)
{
	publish_value("", "net/%s/ap/%s/freq", iface, bssid);
	publish_value("", "net/%s/ap/%s/level", iface, bssid);
	publish_value("", "net/%s/ap/%s/ssid", iface, bssid);
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
	if (!self_ap && curr_bssid[0])
		wpa_send("BSS %s", curr_bssid);
	else
		wpa_send("PING");
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

	if (!mystrncmp("<2>", line) || !mystrncmp("<3>", line)) {
		/* publish line+3 to mqtt log */
		publish_value(line+3, "tmp/%s/wpa", iface);
		tok = strtok(line+3, " \t");
		if (!strcmp(tok, "CTRL-EVENT-CONNECTED")) {
			wpa_send("STATUS");
		} else if (!strcmp(tok, "CTRL-EVENT-DISCONNECTED")) {
			wpa_send("STATUS");
		} else if (!strcmp(tok, "CTRL-EVENT-BSS-ADDED")) {
			strtok(NULL, " \t");
			tok = strtok(NULL, " \t");
			wpa_send("BSS %s", tok);
			have_bss_events = 1;
		} else if (!strcmp(tok, "CTRL-EVENT-BSS-REMOVED")) {
			strtok(NULL, " \t");
			tok = strtok(NULL, " \t");
			remove_ap(find_ap_by_bssid(tok));
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

	} else if (!strcmp("LIST_NETWORKS", head->a)) {
		/* clear network list */
		for (j = 0; j < nnetworks; ++j)
			myfree(networks[j].ssid);
		nnetworks = 0;

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
		}
		sort_networks();

	} else if (!strcmp(head->a, "SCAN_RESULTS")) {
		/* clear BF_PRESENT flag in ap list */
		for (j = 0; j < naps; ++j)
			aps[j].flags &= ~BF_PRESENT;

		/* parse lines */
		char *bssid;
		struct ap *ap;
		for (line = strtok_r(line, "\r\n", &saveptr); line;
				line = strtok_r(NULL, "\r\n", &saveptr)) {
			if (!mystrncmp("bssid", line))
				/* header line */
				continue;
			bssid = strtok(line, "\t");
			/* process like 'hot-detected' bssid's */
			wpa_send("BSS %s", bssid);
			ap = find_ap_by_bssid(bssid);
			/* mark ap as present */
			if (ap)
				ap->flags |= BF_PRESENT;
		}
		for (j = 0; j < naps; ) {
			if (aps[j].flags & BF_PRESENT) {
				++j;
				continue;
			}
			/* remove this ap */
			hide_ap_mqtt(aps[j].bssid);
			remove_ap(aps+j);
		}

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
		struct ap *ap;

		ap = find_ap_by_bssid(bssid);
		if (ap) {
			if (ap->freq != freq)
				publish_value(valuetostr("%.3lfG", freq*1e-3), "net/%s/ap/%s/freq", iface, bssid);
			if (ap->level != level)
				publish_value(valuetostr("%i", level), "net/%s/ap/%s/level", iface, bssid);
			ap->freq = freq;
			ap->level = level;
			if (!self_ap && !strcmp(curr_bssid, bssid ?: "")) {
				if (level != curr_level)
					publish_value(valuetostr("%i", level), "net/%s/level", iface);
				curr_level = level;
			}
		} else if (bssid) {
			add_ap(bssid, freq, level, flags, ssid);
			publish_value(valuetostr("%.3lfG", freq*1e-3), "net/%s/ap/%s/freq", iface, bssid);
			publish_value(valuetostr("%i", level), "net/%s/ap/%s/level", iface, bssid);
			publish_value(ssid, "net/%s/ap/%s/ssid", iface, bssid);
		}
	} else if (!strcmp("STATUS", head->a)) {
		char *val;
		char *ssid = NULL;
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
				self_ap = !strcmp(val, "AP");
		}
		publish_value(curr_bssid, "net/%s/bssid", iface);
		if (self_ap) {
			publish_value(valuetostr("%.3lfG",freq*1e-3), "net/%s/freq", iface);
			publish_value("", "net/%s/level", iface);
			publish_value(ssid, "net/%s/ssid", iface);
		} else if (curr_bssid[0]) {
			publish_value(valuetostr("%.3lfG",freq*1e-3), "net/%s/freq", iface);
			struct ap *ap = find_ap_by_bssid(curr_bssid);
			if (ap) {
				if (curr_level != ap->level)
					publish_value(valuetostr("%i", ap->level), "net/%s/level", iface);
				curr_level = ap->level;
			}
			publish_value(ssid, "net/%s/ssid", iface);
		} else {
			publish_value("", "net/%s/freq", iface);
			publish_value("", "net/%s/level", iface);
			publish_value("", "net/%s/ssid", iface);
			curr_level = 0;
		}

	} else if (!mystrncmp("ADD_NETWORK", head->a)) {
		int id;
		struct network *net;

		id = strtoul(line, NULL, 0);
		net = newnetwork;
		newnetwork = NULL;

		if (!net)
			goto done;
		net->id = id;
		wpa_send("SET_NETWORK %i ssid \"%s\"", id, net->ssid);
		if (net && net->psk) {
			wpa_send("SET_NETWORK %i psk \"%s\"", id, net->psk);
			free(net->psk);
			net->psk = NULL;
		}
		wpa_send("ENABLE_NETWORK %i", id);
	} else if (!mystrncmp("SET_NETWORK ", head->a)) {
		struct str *str;
		for (str = strq; str; str = str->next) {
			if (!mystrncmp("SET_NETWORK", str->a) ||
					!mystrncmp("ENABLE_NETWORK", str->a) ||
					!mystrncmp("DISABLE_NETWORK", str->a) ||
					!mystrncmp("ADD_NETWORK", str->a))
				break;
		}
		if (!str)
			wpa_send("SAVE_CONFIG");
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
	if (ntoks < 3 || strcmp("net", toks[0]) || strcmp(iface, toks[1])) {
	} else if (!strcmp(toks[2], "raw")) {
		wpa_send(msg->payload);
	} else if (!strcmp(toks[2], "scan")) {
		wpa_send("SCAN");
	} else if (!strcmp(toks[2], "ssid") && ntoks >= 4 && !strcmp(toks[3], "set")) {
		/* select new ssid. Do this only for new msgs (!retained) */
		if (msg->payloadlen && strcmp(msg->payload, "all")) {
			struct network *net;

			net = find_network_by_ssid(msg->payload ?: "");
			if (net)
				wpa_send("SELECT_NETWORK %i", net->id);
			else
				mylog(LOG_INFO, "selected unknown network '%s'", (char *)msg->payload ?: "");
		} else
			wpa_send("ENABLE_NETWORK all");
	} else if (ntoks >= 4 && !strcmp(toks[3], "psk")) {
		struct network *net;

		net = find_network_by_ssid(toks[2]);
		if (!net) {
			if (newnetwork) {
				/* too rapid */
				mylog(LOG_WARNING, "previous new ssid still pending");
				return;
			}
			wpa_send("ADD_NETWORK");
			net = add_network(-1, toks[2]);
			net->psk = strndup(msg->payload, msg->payloadlen);
			sort_networks();
			/* sorting invalidates 'net' pointer */
			newnetwork = find_network_by_ssid(toks[2]);
		} else {
			wpa_send("SET_NETWORK %i psk %s", net->id, (char *)msg->payload);
		}
	}
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
	subscribe_topic("net/%s/#", iface);

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
			if (ret < 0)
				mylog(LOG_ERR, "recv wpa: %s", ESTR(errno));
			if (!ret) {
				mylog(LOG_WARNING, "wpa closed");
				break;
			}
			line[ret] = 0;
			wpa_recvd_pkt(line);
		}
		if (pf[1].revents) {
			/* mqtt read ... */
			ret = mosquitto_loop_read(mosq, 1);
			if (ret)
				mylog(LOG_ERR, "mosquitto_loop_read: %s", mosquitto_strerror(ret));
		}
		/* mosquitto things to do each iteration */
		ret = mosquitto_loop_misc(mosq);
		if (ret)
			mylog(LOG_ERR, "mosquitto_loop_misc: %s", mosquitto_strerror(ret));
		if (mosquitto_want_write(mosq)) {
			ret = mosquitto_loop_write(mosq, 1);
			if (ret)
				mylog(LOG_ERR, "mosquitto_loop_write: %s", mosquitto_strerror(ret));
		}
	}

	/* clean scan results in mqtt */
	for (j = 0; j < naps; ++j) {
		publish_value("", "net/%s/ap/%s/freq", iface, aps[j].bssid);
		publish_value("", "net/%s/ap/%s/level", iface, aps[j].bssid);
		publish_value("", "net/%s/ap/%s/ssid", iface, aps[j].bssid);
	}
	publish_value("", "net/%s/bssid", iface);
	publish_value("", "net/%s/freq", iface);
	publish_value("", "net/%s/level", iface);
	publish_value("", "net/%s/ssid", iface);

	/* terminate */
	send_self_sync(mosq, mqtt_qos);
	while (!ready) {
		ret = mosquitto_loop(mosq, 10, 1);
		if (ret < 0)
			mylog(LOG_ERR, "mosquitto_loop: %s", mosquitto_strerror(ret));
	}

#if 0
	/* free memory */
	for (j = 0; j < naps; ++j)
		myfree(aps[j].ssid);
	myfree(aps);
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
