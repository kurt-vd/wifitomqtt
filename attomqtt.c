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
#include <sys/signalfd.h>
#include <sys/uio.h>
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
	" -o, --options=OPT[,OPT...]	tune additional options\n"
	"				turn off options that are prefixed with no-\n"
	"	csq[=DELAY]	Enable periodic signal monitor (AT+CSQ)\n"
	"			AT+CSQ is done once each DELAY seconds (default 10)\n"
	"	cnti[=DELAY]	Enable periodic technology monitor (AT*CNTI)\n"
	"			AT*CNTI=0 is done once each DELAY seconds (default 10)\n"
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

	{ "options", required_argument, NULL, 'o', },
	{ },
};
#else
#define getopt_long(argc, argv, optstring, longopts, longindex) \
	getopt((argc), (argv), (optstring))
#endif
static const char optstring[] = "Vv?h:p:o:";

static char *const subopttable[] = {
	"csq",
#define O_CSQ		(1 << 0)
	"cnti",
#define O_CNTI		(1 << 1)
	"cops",
#define O_COPS		(1 << 2)
	NULL,
};

/* signal handler */
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

/* utils */
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
static int ignore_responses;
static int options;
static double csq_delay = 10;
static double cnti_delay = 10;
/* raw rssi & ber values, 99 equals 'no value' */
static int saved_rssi = 99, saved_ber = 99;
static char *saved_op;
static char *saved_nt0;

/* command queue */
struct str {
	struct str *next;
	char a[1];
};

static struct str *strq, *strqlast;
static int cmd_pending;

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

/* AT iface */
__attribute__((format(printf,1,2)))
static int at_write(const char *fmt, ...);
/* low-level write */
static int at_ll_write(const char *str);

static void at_next_cmd(void)
{
	struct str *head;

	head = pop_strq();
	if (head) {
		at_ll_write(head->a);
		free(head);
	}
}

static void at_timeout(void *dat)
{
	mypublish("fail", "timeout", 0);
	mylog(LOG_WARNING, "AT command timeout");
	cmd_pending = 0;
	at_next_cmd();
}

static void at_recvd_response(int argc, char *argv[])
{
	char *endp, *tok, *str;
	static char buf[1024*16], *pbuf;

	if (!strcmp(argv[0], ""))
		/* unknown command, echo was off? */
		return;
	else if (!strcmp(argv[0], "RING")) {
	} else if (strcmp(argv[argc-1], "OK")) {
		mypublish("fail", valuetostr("%s: %s", argv[0], argv[argc-1]), 0);
		mylog(LOG_WARNING, "Command '%s': %s", argv[0], argv[argc-1]);
	} else if (!strcasecmp(argv[0], "AT+CSQ")) {
		int rssi, ber;

		/* response[1] is of format: '+CSQ: <RSSI>,<BER>' */
		if (strncasecmp(argv[1], "+CSQ: ", 6))
			return;
		rssi = strtoul(argv[1]+6, &endp, 0);
		if (rssi != saved_rssi) {
			mypublish("rssi", (rssi == 99) ? NULL : valuetostr("%i", -113 + 2*rssi), 1);
			saved_rssi = rssi;
		}

		/* bit-error-rate */
		ber = strtoul(endp+1, NULL, 0);
		static const char *const ber_values[] = {
			[0] = "<0.01%",
			[1] = "0.01% -- 0.1%",
			[2] = "0.1% -- 0.5%",
			[3] = "0.5% -- 1%",
			[4] = "1% -- 2%",
			[5] = "2% -- 4%",
			[6] = "4% -- 8%",
		};
		if (ber != saved_ber) {
			mypublish("ber", (ber >= sizeof(ber_values)/sizeof(ber_values[0])) ? NULL : ber_values[ber], 1);
			saved_ber = ber;
		}
	} else if (!strcasecmp(argv[0], "at*cnti=0") ||
			!strcasecmp(argv[0], "at*cnti?")) {
		if (strncasecmp(argv[1], "*cnti: 0,", 9))
			return;
		tok = argv[1]+9;
		if (strcmp(tok ?: "", saved_nt0 ?: "")) {
			myfree(saved_nt0);
			saved_nt0 = tok ? strdup(tok) : NULL;
			mypublish("nt", tok, 1);
		}

	} else if (!strcasecmp(argv[0], "at+cops?")) {
		/* current operator */
		char *op;

		if (strncasecmp(argv[1], "+cops: ", 7))
			return;
		/* mode,format,"operator",tech */
		strtok(argv[1], ",");
		strtok(NULL, ",");
		op = strtok(NULL, ",");
		//strtok(NULL, ",");
		if (op) {
			int len = strlen(op);
			if (*op == '"' && op[len-1] == '"') {
				op[len-1] = 0;
				++op;
			} else
				/* NUMERIC ? */
				op = NULL;
		}
		if (strcmp(op ?: "", saved_op ?: "")) {
			mypublish("op", op, 1);
			myfree(saved_op);
			saved_op = op ? strdup(op) : NULL;
		}
	} else if (!strcasecmp(argv[0], "at+cops=?")) {
		/* operator list */
		int stat;
		if (strncasecmp(argv[1], "+cops: ", 7))
			return;
		str = argv[1]+7;
		pbuf = buf;
		for (; *str == '('; str = endp ?: "") {
			++str;
			endp = strstr(str, "),");
			if (endp) {
				*endp = 0;
				endp += 2;
			}
			/* parse operator */
			stat = strtoul(strtok(str, ",\""), NULL, 0);
			tok = strtok(NULL, ",\"");
			/* append operator to txbuf */
			if (pbuf > buf)
				/* insert seperator */
				*pbuf++ = ',';
			/* prepend state character: unknown, available, current, not allowed */
			*pbuf++ = (stat < 4) ? "? *-"[stat] : '?';
			strcpy(pbuf, tok);
			pbuf += strlen(pbuf);
		}
		mypublish("ops", buf, 0);
	}
}

static void at_recvd(char *line)
{
	char *str, *sep;
	static char buf[1024*16], reconstructed[1024*16];
	static int consumed, fill;
#define NARGV 32
	static char *argv[NARGV];
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
			continue;
		}
		/* collect response */
		argv[argc++] = str;
		if (argc > NARGV-1) {
			/* drop items */
			--argc;
			argv[argc-1] = "...";
		}
		if (!strcmp(str, "OK") ||
				!strcmp(str, "NO CARRIER") ||
				!strncmp(str, "+CME ERROR", 10) ||
				!strcmp(str, "ABORT") ||
				!strcmp(str, "ERROR")) {
			/* queue admin */
			cmd_pending = 0;
			libt_remove_timeout(at_timeout, NULL);
			at_next_cmd();
			/* process this command */
			if (ignore_responses > 0) {
				--ignore_responses;
				goto response_done;
			}
			/* reconstruct clean packet */
			for (str = reconstructed, j = 0; j < argc; ++j) {
				if (j)
					*str++ = '\t';
				strcpy(str, argv[j]);
				str += strlen(str);
			}
			*str = 0;
			/* publish raw response */
			mypublish("at", reconstructed, 0);

			/* process */
			argv[argc] = NULL;
			at_recvd_response(argc, argv);
			/* restart response collection */
response_done:
			argc = 0;
		}
	}
	if (consumed >= fill && !argc)
		consumed = fill = 0;
}

/* AT API */
static int at_ll_write(const char *str)
{
	struct iovec vec[2] = {
		[0] = { .iov_base = (void *)str, .iov_len = strlen(str), },
		[1] = { .iov_base = "\r\n", .iov_len = 2, },
	};
	int ret;

	ret = writev(atsock, vec, 2);
	if (ret <= 0) {
		mypublish("fail", valuetostr("dprintf %s %7s: %s", atdev, str, ret ? ESTR(errno) : "eof"), 0);
		mylog(LOG_WARNING, "dprintf %s %7s: %s", atdev, str, ret ? ESTR(errno) : "eof");
	} else {
		double timeout = 5;
		if (!strcasecmp(str, "at+cops=?"))
			/* operator scan takes time */
			timeout = 60;
		cmd_pending = 1;
		libt_add_timeout(timeout, at_timeout, NULL);
	}
	return ret;
}

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

	if (!cmd_pending)
		return at_ll_write(buf);
	/* enter queue */
	add_strq(buf);
	return 0;
}

static void at_ifnotqueued(const char *atcmd)
{
	struct str *str;

	for (str = strq; str; str = str->next) {
		if (!strcmp(atcmd, str->a))
			return;
	}
	/* queue a new entry */
	at_write("%s", atcmd);
}

static void at_csq(void *dat)
{
	at_ifnotqueued("at+csq");
	/* repeat */
	libt_add_timeout(csq_delay, at_csq, dat);
}

static void at_cnti(void *dat)
{
	at_ifnotqueued("at*cnti=0");
	/* repeat */
	libt_add_timeout(cnti_delay, at_cnti, dat);
}

static void at_cops(void *dat)
{
	at_ifnotqueued("at+cops?");
	/* repeat */
	libt_add_timeout(300, at_cops, dat);
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
	int opt, ret, not;
	char *str, *subopts, *savedstr;
	char mqtt_name[32];
	struct pollfd pf[3];
	int sigfd;
	struct signalfd_siginfo sfdi;
	sigset_t sigmask;

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

	case 'o':
		subopts = optarg;
		while (*subopts) {
			savedstr = subopts;
			not = !strncmp(subopts, "no-", 3);
			if (not)
				subopts += 3;
			opt = getsubopt(&subopts, subopttable, &optarg);
			if (opt < 0) {
				fprintf(stderr, "%s: option '%s' unknown\n", program_invocation_short_name, savedstr);
				fputs(help_msg, stderr);
				return 1;
			}
			opt = 1 << opt;
			/* make sure O_xxx & FL_xxx correspond */
			if (not)
				options &= ~opt;
			else
				options |= opt;
			switch (opt) {
			case O_CSQ:
				if (optarg)
					csq_delay = strtod(optarg, NULL);
				break;
			case O_CNTI:
				if (optarg)
					cnti_delay = strtod(optarg, NULL);
				break;
			};
		}
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

	/* prepare signalfd */
	sigemptyset(&sigmask);
	sigaddset(&sigmask, SIGINT);
	sigaddset(&sigmask, SIGTERM);
	sigaddset(&sigmask, SIGALRM);

	if (sigprocmask(SIG_BLOCK, &sigmask, NULL) < 0)
		mylog(LOG_ERR, "sigprocmask: %s", ESTR(errno));
	sigfd = signalfd(-1, &sigmask, SFD_NONBLOCK | SFD_CLOEXEC);
	if (sigfd < 0)
		mylog(LOG_ERR, "signalfd failed: %s", ESTR(errno));

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
	pf[2].fd = sigfd;
	pf[2].events = POLL_IN;

	libt_add_timeout(0, do_mqtt_maintenance, mosq);
	/* initial sync */
	at_write("at");
	ignore_responses = 1;
	/* enable echo */
	at_write("ate1");
	at_write("at+cpin?");
	if (options & O_CSQ)
		at_csq(NULL);
	if (options & O_CNTI)
		at_cnti(NULL);
	if (options & O_COPS) {
		/* set alphanumeric operator names */
		at_write("at+cops=3,0");
		at_cops(NULL);
	}
	for (;;) {
		libt_flush();
		if (mosquitto_want_write(mosq)) {
			ret = mosquitto_loop_write(mosq, 1);
			if (ret)
				mylog(LOG_ERR, "mosquitto_loop_write: %s", mosquitto_strerror(ret));
		}
		ret = poll(pf, 3, libt_get_waittime());
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
	if (saved_rssi != 99)
		/* clear rssi */
		mypublish("rssi", NULL, 1);
	if (saved_ber != 99)
		/* clear rssi */
		mypublish("ber", NULL, 1);
	if (saved_op)
		mypublish("op", NULL, 1);
	if (saved_nt0)
		mypublish("nt", NULL, 1);

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
	return 0;
}
