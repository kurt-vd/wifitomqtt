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
#include <termios.h>
#include <syslog.h>
#include <mosquitto.h>

#include "libet/libt.h"
#include "common.h"

#define NAME "attomqtt"
#ifndef VERSION
#define VERSION "<undefined version>"
#endif

#define ESTR(num)	strerror(num)

/* program options */
static const char help_msg[] =
	NAME ": control modem using AT commands via MQTT\n"
	"usage:	" NAME " [OPTIONS ...] DEVICE\n"
	"\n"
	"Options\n"
	" -V, --version		Show version\n"
	" -v, --verbose		Be more verbose\n"
	"\n"
	" -h, --host=HOST[:PORT]Specify alternate MQTT host+port\n"
	" -p, --prefix=PREFIX	Use MQTT topic prefix (default: net/TTYNAME/)\n"
	"\n"
	"Arguments\n"
	" DEVICE	TTY device for modem\n"
	;

#ifdef _GNU_SOURCE
static struct option long_opts[] = {
	{ "help", no_argument, NULL, '?', },
	{ "version", no_argument, NULL, 'V', },
	{ "verbose", no_argument, NULL, 'v', },

	{ "host", required_argument, NULL, 'h', },
	{ "prefix", required_argument, NULL, 'p', },
	{ },
};
#else
#define getopt_long(argc, argv, optstring, longopts, longindex) \
	getopt((argc), (argv), (optstring))
#endif
static const char optstring[] = "Vv?h:p:";

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
static char *mqtt_prefix;
static int mqtt_prefix_len;

/* state */
static struct mosquitto *mosq;
static void mypublish(const char *bare_topic, const char *value, int retain);
__attribute__((format(printf,1,2)))
static const char *valuetostr(const char *fmt, ...);

__attribute__((unused))
static void myfree(void *dat)
{
	if (dat)
		free(dat);
}

/* AT */
static const char *atdev;
static int atsock;
static int ncmds;

/* AT iface */
static void at_timeout(void *dat)
{
	mypublish("fail", "timeout", 0);
	mylog(LOG_WARNING, "AT command timeout");
}

static void at_recvd_response(int argc, char *argv[])
{
	if (!strcmp(argv[0], ""))
		/* unknown command, echo was off? */
		return;
	else if (!strcmp(argv[0], "RING")) {
	} else if (strcmp(argv[argc-1], "OK")) {
		mypublish("fail", valuetostr("%s: %s", argv[0], argv[argc-1]), 0);
		mylog(LOG_WARNING, "Command '%s': %s", argv[0], argv[argc-1]);
	}
}

static void at_recvd(char *line)
{
	char *str, *sep;
	static char buf[1024*16], reconstructed[1024*16];
	static int consumed, fill;
	static char *argv[32];
	static int argc;
	int len, j;

	len = strlen(line);
	if (fill+len+1 >= sizeof(buf) && consumed) {
		memmove(buf, buf+consumed, fill+1-consumed);
		/* adapt the strings in argv for the new position */
		for (j = 0; j < argc; ++j)
			argv[j] -= consumed;
		fill -= consumed;
		consumed = 0;
	}
	if (fill+len+1 >= sizeof(buf))
		mylog(LOG_ERR, "buffer full, no completed command");
	strcpy(buf+fill, line);
	fill += len;

	for (sep = buf+consumed; *sep;) {
		str = sep;
		sep = strchr(str, '\n');
		if (sep)
			*sep++ = 0;
		/* '*line' indicates we're not eof yet */
		if (!sep && *line)
			break;
		consumed = sep ? sep - buf : fill;
		if (!strncmp(str, "RING", 4)) {
			static char *ring_argv[2];
			/* indicate ring */
			ring_argv[0] = str;
			mypublish("echo", argv[0], 0);
			at_recvd_response(1, ring_argv);
			if (ncmds)
				/* postpone timeout */
				libt_add_timeout(5, at_timeout, NULL);
			continue;
		}
		/* collect response */
		argv[argc++] = str;
		if (!strcmp(str, "OK") ||
				!strcmp(str, "NO CARRIER") ||
				!strcmp(str, "ABORT") ||
				!strcmp(str, "ERROR")) {
			--ncmds;
			if (ncmds < 0)
				/* command underflow is possible if someone insert commands
				 * directly in the tty device
				 */
				ncmds = 0;
			if (ncmds)
				/* set next timeout */
				libt_add_timeout(5, at_timeout, NULL);
			else
				libt_remove_timeout(at_timeout, NULL);
			/* reconstruct clean packet */
			for (str = reconstructed, j = 0; j < argc; ++j) {
				if (j)
					*str++ = '\n';
				strcpy(str, argv[j]);
				str += strlen(str);
			}
			*str = 0;
			/* publish raw response */
			mypublish("echo", reconstructed, 0);

			/* process */
			argv[argc] = NULL;
			at_recvd_response(argc, argv);
			/* restart response collection */
			argc = 0;
		}
	}
	if (consumed >= fill && !argc)
		consumed = fill = 0;
}

/* MQTT API */
static int at_write(const char *fmt, ...)
{
	static char buf[1024];
	int ret;
	va_list va;

	va_start(va, fmt);
	ret = vsprintf(buf, fmt, va);
	va_end(va);

	if (ret <= 0)
		return ret;

	ret = dprintf(atsock, "%s\r\n", buf);
	if (ret <= 0) {
		mypublish("fail", valuetostr("dprintf %s %7s: %s", atdev, buf, ret ? ESTR(errno) : "eof"), 0);
		mylog(LOG_WARNING, "dprintf %s %7s: %s", atdev, buf, ret ? ESTR(errno) : "eof");
		return ret;
	}
	++ncmds;
	libt_add_timeout(5, at_timeout, NULL);
	return ret;
}

/* MQTT iface */
static void my_mqtt_msg(struct mosquitto *mosq, void *dat, const struct mosquitto_message *msg)
{
	if (is_self_sync(msg)) {
		ready = 1;
		return;
	}

	if (strncmp(mqtt_prefix, msg->topic, mqtt_prefix_len))
		return;

	if (!strcmp(msg->topic+mqtt_prefix_len, "at/set"))
		at_write("%s", (char *)msg->payload);
}

static const char *valuetostr(const char *fmt, ...)
{
	va_list va;
	static char value[1024];

	va_start(va, fmt);
	vsprintf(value, fmt, va);
	va_end(va);

	return value;
}
static void mypublish(const char *bare_topic, const char *value, int retain)
{
	int ret;
	static char topic[1024];

	sprintf(topic, "%s%s", mqtt_prefix, bare_topic);

	/* publish cache */
	ret = mosquitto_publish(mosq, NULL, topic, strlen(value ?: ""), value, mqtt_qos, retain);
	if (ret < 0)
		mylog(LOG_ERR, "mosquitto_publish %s: %s", topic, mosquitto_strerror(ret));
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
	int opt, ret;
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
	case 'p':
		mqtt_prefix = optarg;
		break;

	default:
		fprintf(stderr, "unknown option '%c'", opt);
	case '?':
		fputs(help_msg, stderr);
		exit(1);
		break;
	}

	if (!argv[optind]) {
		fprintf(stderr, "no tty given\n");
		fputs(help_msg, stderr);
		exit(1);
	}

	setmylog(NAME, 0, LOG_LOCAL2, loglevel);

	/* prepare program */
	atdev = argv[optind];
	if (!mqtt_prefix) {
		str = strrchr(atdev, '/');
		if (str)
			++str;
		asprintf(&mqtt_prefix, "%s/", str);
		mylog(LOG_INFO, "mqtt prefix set to %s", mqtt_prefix);
	}
	mqtt_prefix_len = strlen(mqtt_prefix);

	/* AT */
	atsock = open(atdev, O_RDWR | O_NOCTTY | O_CLOEXEC | O_NONBLOCK);
	if (atsock < 0)
		mylog(LOG_ERR, "open %s: %s", atdev, ESTR(errno));

	struct termios tio;
	if (tcgetattr(atsock, &tio) < 0)
		mylog(LOG_ERR, "tcgetattr %s failed: %s", atdev, ESTR(errno));
	/* drop incoming CR
	 * The idea here is to emit \r\n to the modem
	 * and to strip \r on the input.
	 * That makes parser life way simpler!
	 */
	tio.c_iflag |= IGNCR;
	if (tcsetattr(atsock, TCSANOW, &tio) < 0)
		mylog(LOG_ERR, "tcsetattr %s failed: %s", atdev, ESTR(errno));

	/* MQTT start */
	if (mqtt_qos < 0)
		mqtt_qos = !strcmp(mqtt_host ?: "", "localhost") ? 0 : 1;
	mosquitto_lib_init();
	sprintf(mqtt_name, "%s-%i", NAME, getpid());
	mosq = mosquitto_new(mqtt_name, true, NULL);
	if (!mosq)
		mylog(LOG_ERR, "mosquitto_new failed: %s", ESTR(errno));

	ret = mosquitto_connect(mosq, mqtt_host, mqtt_port, mqtt_keepalive);
	if (ret)
		mylog(LOG_ERR, "mosquitto_connect %s:%i: %s", mqtt_host, mqtt_port, mosquitto_strerror(ret));
	mosquitto_message_callback_set(mosq, my_mqtt_msg);
	subscribe_topic("%sat/set", mqtt_prefix);

	/* prepare poll */
	pf[0].fd = atsock;
	pf[0].events = POLL_IN;
	pf[1].fd = mosquitto_socket(mosq);
	pf[1].events = POLL_IN;

	libt_add_timeout(0, do_mqtt_maintenance, mosq);
	/* enable echo */
	at_write("ate1");
	while (!sigterm) {
		libt_flush();
		if (mosquitto_want_write(mosq)) {
			ret = mosquitto_loop_write(mosq, 1);
			if (ret)
				mylog(LOG_ERR, "mosquitto_loop_write: %s", mosquitto_strerror(ret));
		}
		ret = poll(pf, 2, libt_get_waittime());
		if (ret < 0 && errno == EINTR)
			continue;
		if (ret < 0)
			mylog(LOG_ERR, "poll ...");
		while (pf[0].revents) {
			static char line[1024];
			/* read input events */
			ret = read(atsock, line, sizeof(line)-1);
			if (ret < 0 && errno == EINTR)
				continue;
			if (ret < 0 && errno == EAGAIN)
				break;
			if (ret < 0)
				mylog(LOG_ERR, "recv AT: %s", ESTR(errno));
			line[ret] = 0;
			at_recvd(line);
			if (!ret) {
				mylog(LOG_WARNING, "%s EOF", atdev);
				goto done;
			}
		}
		if (pf[1].revents) {
			/* mqtt read ... */
			ret = mosquitto_loop_read(mosq, 1);
			if (ret) {
				mylog(LOG_WARNING, "mosquitto_loop_read: %s", mosquitto_strerror(ret));
				break;
			}
		}
	}

done:

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
