/*
 * Copyright 2019 Kurt Van Dijck <dev.kurt@vandijck-laurijssen.be>
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
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <unistd.h>
#include <getopt.h>
#include <fcntl.h>
#include <syslog.h>

#include <mosquitto.h>

#define NAME "atinsert"
#ifndef VERSION
#define VERSION "<undefined version>"
#endif

/* generic error logging */
#define mylog(loglevel, fmt, ...) \
	({\
		if (loglevel <= maxloglevel) {\
			fprintf(stderr, "%s: " fmt "\n", NAME, ##__VA_ARGS__);\
			fflush(stderr); \
		}\
		if (loglevel <= LOG_ERR)\
			exit(1);\
	})
#define ESTR(num)	strerror(num)

/* program options */
static const char help_msg[] =
	NAME ": Insert AT command and wait for result via attomqtt muxer\n"
	"usage:	" NAME " [OPTIONS ...] ATCMD\n"
	"\n"
	"Options\n"
	" -V, --version		Show version\n"
	" -v, --verbose		Be more verbose\n"
	" -h, --host=HOST	Set hostname\n"
	" -t, --topic=TOPIC	Send to TOPIC/raw/send\n"
	" -i, --iface=NETDEV	Send to net/NETDEV/raw/send\n"
	" -x, --exitonfailure	Exit with failure on unsuccessfull command\n"
	"			Give twice to exit immediately\n"
	" -w, --wait=TIME	Abort after TIME seconds (default 5)\n"
	"\n"
	"Arguments\n"
	" ATCMD		string to send to the modem\n"
	;

#ifdef _GNU_SOURCE
static struct option long_opts[] = {
	{ "help", no_argument, NULL, '?', },
	{ "version", no_argument, NULL, 'V', },
	{ "verbose", no_argument, NULL, 'v', },

	{ "host", required_argument, NULL, 'h', },
	{ "topic", required_argument, NULL, 't', },
	{ "iface", required_argument, NULL, 'i', },
	{ "exitonfialure", no_argument, NULL, 'x', },
	{ "wait", required_argument, NULL, 'w', },
	{ },
};
#else
#define getopt_long(argc, argv, optstring, longopts, longindex) \
	getopt((argc), (argv), (optstring))
#endif
static const char optstring[] = "Vv?h:t:i:xw:";

/* configuration */
static int maxloglevel = LOG_WARNING;
static char *topicbase = "net/ppp0";
static char *topicsend;
static char *topicrecv;
static int failexit;

static const char *mqtt_host = "localhost";
static int mqtt_port = 1883;
static int mqtt_keepalive = 10;
static int mqtt_qos = 1;

/* state */
struct mosquitto *mosq;
static char **cmds;
static int failed = 0;

static void my_mqtt_msg(struct mosquitto *mosq, void *userdata, const struct mosquitto_message *mmsg)
{
	int ret;
	char *msg, *tok, *sep;

	if ((failexit > 1 && failed) || !mmsg->payload || !*cmds)
		/* empty msg, or no more commands */
		return;
	/* test if message starts with our own command */
	msg = mmsg->payload;
	/* find first token: command echo */
	sep = strchr(msg, '\t');
	if (!sep)
		return;
	if (strncmp(*cmds, msg, sep - msg) || (*cmds)[sep - msg] != 0)
		return;

	printf("%s\n", msg);

	if (failexit) {
		/* find last token: result code */
		tok = strrchr(msg, '\t');
		if (tok && strcmp("OK", tok+1)) {
			failed = 1;
			if (failexit > 1)
				goto terminate;
		}
	}
	++cmds;
	if (!*cmds) {
		failed = 0;
		goto terminate;
	}

	if (failexit > 1) {
		ret = mosquitto_publish(mosq, NULL, topicsend, strlen(*cmds), *cmds, mqtt_qos, 0);
		if (ret)
			mylog(LOG_ERR, "mosquitto_publish %s=%s: %s", topicsend, *cmds, mosquitto_strerror(ret));
	}
	return;
terminate:
	/* terminate loop */
	mosquitto_disconnect(mosq);
}

int main(int argc, char *argv[])
{
	int opt, ret, j;

	/* default wait 10 seconds */
	alarm(5);
	/* argument parsing */
	while ((opt = getopt_long(argc, argv, optstring, long_opts, NULL)) >= 0)
	switch (opt) {
	case 'V':
		fprintf(stderr, "%s %s\nCompiled on %s %s\n",
				NAME, VERSION, __DATE__, __TIME__);
		exit(0);
	case 'v':
		++maxloglevel;
		break;
	case 'h':
		mqtt_host = optarg;
		break;
	case 't':
		topicbase = optarg;
		break;
	case 'i':
		/* malloc new topicbase, memory is lost */
		asprintf(&topicbase, "net/%s", optarg);
		break;
	case 'x':
		++failexit;
		break;
	case 'w':
		alarm(strtoul(optarg, NULL, 10));
		break;

	default:
		fprintf(stderr, "unknown option '%c'", opt);
	case '?':
		fputs(help_msg, stderr);
		exit(1);
		break;
	}

	if (!argv[optind]) {
		mylog(LOG_WARNING, "no ATCMD given");
		fputs(help_msg, stderr);
		exit(1);
	}
	/* prepare */
	cmds = argv+optind;
	asprintf(&topicsend, "%s/raw/send", topicbase);
	asprintf(&topicrecv, "%s/raw/at", topicbase);

	/* MQTT start */
	char mqttname[128];
	mosquitto_lib_init();
	sprintf(mqttname, "%s-%i", NAME, getpid());
	mosq = mosquitto_new(mqttname, true, 0);
	if (!mosq)
		mylog(LOG_ERR, "mosquitto_new failed: %s", ESTR(errno));
	/* mosquitto_will_set(mosq, "TOPIC", 0, NULL, mqtt_qos, 1); */

	mosquitto_message_callback_set(mosq, my_mqtt_msg);

	ret = mosquitto_connect(mosq, mqtt_host, mqtt_port, mqtt_keepalive);
	if (ret)
		mylog(LOG_ERR, "mosquitto_connect %s:%i: %s", mqtt_host, mqtt_port, mosquitto_strerror(ret));

	/* subscribe */
	ret = mosquitto_subscribe(mosq, NULL, topicrecv, mqtt_qos);
	if (ret)
		mylog(LOG_ERR, "mosquitto_subscribe '%s': %s", topicrecv, mosquitto_strerror(ret));

	/* send commands in MQTT */
	for (j = optind; j < argc; ++j) {
		ret = mosquitto_publish(mosq, NULL, topicsend, strlen(argv[j]), argv[j], mqtt_qos, 0);
		if (ret)
			mylog(LOG_ERR, "mosquitto_publish %s=%s: %s", topicsend, argv[j], mosquitto_strerror(ret));
		if (failexit > 1)
			/* only send commands when the previous one succeeded */
			break;
	}
	/* main loop */
	mosquitto_loop_forever(mosq, -1, 1);

	/* finally ... */
	mosquitto_destroy(mosq);
	mosquitto_lib_cleanup();
	return failed;
}
