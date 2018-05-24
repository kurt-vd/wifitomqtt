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
#include <ifaddrs.h>
#include <locale.h>
#include <poll.h>
#include <syslog.h>
#include <arpa/inet.h>
#include <net/if.h>
#include <mosquitto.h>

#include "libet/libt.h"
#include "common.h"

#define NAME "ifaddrtomqtt"
#ifndef VERSION
#define VERSION "<undefined version>"
#endif

#define ESTR(num)	strerror(num)

/* program options */
static const char help_msg[] =
	NAME ": Emit ifaddr's to MQTT\n"
	"usage:	" NAME " [OPTIONS ...]\n"
	"\n"
	"Options\n"
	" -V, --version		Show version\n"
	" -v, --verbose		Be more verbose\n"
	"\n"
	" -h, --host=HOST[:PORT]Specify alternate MQTT host+port\n"
	;

#ifdef _GNU_SOURCE
static struct option long_opts[] = {
	{ "help", no_argument, NULL, '?', },
	{ "version", no_argument, NULL, 'V', },
	{ "verbose", no_argument, NULL, 'v', },

	{ "host", required_argument, NULL, 'h', },

	{ },
};
#else
#define getopt_long(argc, argv, optstring, longopts, longindex) \
	getopt((argc), (argv), (optstring))
#endif
static const char optstring[] = "Vv?h:";

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

/* ADDR */
struct iface {
	char name[IFNAMSIZ+1];
	char *prevvalue;
	char *value;
	int nvalue, svalue;
};

static struct iface *ifaces;
static int nifaces, sifaces;

static struct iface *add_iface(const char *name)
{
	struct iface *iface;

	if (nifaces+1 > sifaces) {
		sifaces += 16;
		ifaces = realloc(ifaces, sizeof(*ifaces)*sifaces);
		if (!ifaces)
			mylog(LOG_ERR, "realloc %i ifaces: %s", sifaces, ESTR(errno));
	}
	iface = &ifaces[nifaces++];
	memset(iface, 0, sizeof(*iface));

	strncpy(iface->name, name, sizeof(iface->name)-1);
	return iface;
}

static void remove_iface(struct iface *iface)
{
	int idx = iface - ifaces;

	myfree(iface->value);
	myfree(iface->prevvalue);
	if (idx != nifaces-1) {
		memcpy(ifaces+idx, ifaces+nifaces-1, sizeof(*ifaces));
	}
	--nifaces;
}

static int ifacecmp(const void *a, const void *b)
{
	const struct iface *ia = a, *ib = b;

	return strcmp(ia->name, ib->name);
}

static inline void sort_ifaces(void)
{
	qsort(ifaces, nifaces, sizeof(*ifaces), ifacecmp);
}

static struct iface *find_iface_by_name(const char *iface, int create)
{
	struct iface *result;
	struct iface needle = {};

	strncpy(needle.name, iface, sizeof(needle.name)-1);

	result = bsearch(&needle, ifaces, nifaces, sizeof(*ifaces), ifacecmp);
	if (!result && create) {
		add_iface(iface);
		sort_ifaces();
		/* search again, should produce a result */
		result = find_iface_by_name(iface, 0);
	}
	return result;
}

/* MQTT */
static void my_mqtt_msg(struct mosquitto *mosq, void *dat, const struct mosquitto_message *msg)
{
	if (is_self_sync(msg))
		ready = 1;
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

static const char *addrtostr(const struct sockaddr *addr)
{
	static char buf[1024];

	switch (addr->sa_family) {
	case AF_INET:
		if (!inet_ntop(addr->sa_family, &((struct sockaddr_in *)addr)->sin_addr,
				buf, sizeof(buf)-1))
			return NULL;
		if (!strncmp(buf, "169.254.", 8))
			return NULL;
		break;
	case AF_INET6:
		if (!inet_ntop(addr->sa_family, &((struct sockaddr_in6 *)addr)->sin6_addr,
				buf, sizeof(buf)-1))
			return NULL;
		if (!strncmp(buf, "fe", 2))
			return NULL;
		break;
	default:
		return NULL;
	}
	return buf;
}

static void publish_addrs(void *dat)
{
	struct iface *iface;

	/* reset composer */
	for (iface = ifaces; iface < ifaces+nifaces; ++iface) {
		if (iface->nvalue)
			iface->value[0] = 0;
		iface->nvalue = 0;
	}
	/* compose */
	struct ifaddrs *table = NULL, *ptr;
	int len;
	const char *value;

	/* fetch data */
	if (getifaddrs(&table) < 0)
		mylog(LOG_ERR, "getifaddrs failed: %s", ESTR(errno));

	/* print results */
	for (ptr = table; ptr; ptr = ptr->ifa_next) {
		if (!ptr->ifa_addr)
			continue;
		value = addrtostr(ptr->ifa_addr);
		if (!value)
			continue;
		len = strlen(value);
		/* append value to iface */
		iface = find_iface_by_name(ptr->ifa_name, 1);
		if (iface->nvalue + 1+len+1 > iface->svalue) {
			iface->svalue += len+2;
			/* align size */
			iface->svalue = (iface->svalue +63) & ~63;
			iface->value = realloc(iface->value, iface->svalue);
			if (!iface->value)
				mylog(LOG_ERR, "realloc %u: %s", iface->svalue, ESTR(errno));
		}
		/* insert seperator */
		if (iface->nvalue)
			iface->value[iface->nvalue++] = ' ';
		strcpy(iface->value+iface->nvalue, value);
		iface->nvalue += len;
	}
	/* dispose */
	freeifaddrs(table);

	/* publish */
	int need_sort = 0;
	for (iface = ifaces; iface < ifaces+nifaces; ++iface) {
		if (!strcmp(iface->prevvalue ?: "", iface->value ?: ""))
			continue;

		publish_value(iface->value, "net/%s/addr", iface->name);
		if (!iface->value || !iface->value[0]) {
			remove_iface(iface);
			--iface;
			need_sort = 1;
		} else {
			myfree(iface->prevvalue);
			iface->prevvalue = strdup(iface->value ?: "");
		}
	}
	if (need_sort)
		sort_ifaces();
	libt_add_timeout(1, publish_addrs, dat);
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

	/* prepare poll */
	pf[0].fd = mosquitto_socket(mosq);
	pf[0].events = POLL_IN;
	/* fire first publish */
	publish_addrs(NULL);

	while (!sigterm) {
		libt_flush();
		ret = poll(pf, 1, libt_get_waittime());
		if (ret < 0 && errno == EINTR)
			continue;
		if (ret < 0)
			mylog(LOG_ERR, "poll ...");
		if (pf[0].revents) {
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
	for (j = 0; j < nifaces; ++j)
		publish_value("", "net/%s/addr", ifaces[j].name);

	/* terminate */
	send_self_sync(mosq, mqtt_qos);
	while (!ready) {
		ret = mosquitto_loop(mosq, 10, 1);
		if (ret < 0)
			mylog(LOG_ERR, "mosquitto_loop: %s", mosquitto_strerror(ret));
	}

#if 0
	/* free memory */
	while (nifaces)
		remove_iface(ifaces+nifaces-1);
	myfree(ifaces);

	mosquitto_disconnect(mosq);
	mosquitto_destroy(mosq);
	mosquitto_lib_cleanup();
#endif
	return !sigterm;
}
