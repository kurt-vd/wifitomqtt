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
	"	autocsq		Enable automatic signal reporting (AT+AUTOCSQ=1,1)\n"
	"	creg[=DELAY]	Enable periodic Registration monitoring\n"
	"	cgreg[=DELAY]	Enable periodic GPRS Registration monitoring\n"
	"	cnti[=DELAY]	Enable periodic technology monitor (AT*CNTI)\n"
	"			AT*CNTI=0 is done once each DELAY seconds (default 10)\n"
	"	cops[=DELAY]	Enable periodic operator monitoring\n"
	"	simcom		Enable hack that waits for 'SMS DONE' EONS report after\n"
	"			unsolicited '+SIM: READY', since simcom modems throw those EONS report\n"
	"			in between regular output\n"
	"	detachedscan	Run scan when modem is not registered, i.e. detach before scan\n"
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
	"autocsq",
#define O_AUTOCSQ	(1 << 3)
	"creg",
#define O_CREG		(1 << 4)
	"cgreg",
#define O_CGREG		(1 << 5)
	"simcom",
#define O_SIMCOM	(1 << 6)
	"detachedscan",
#define O_DETACHEDSCAN	(1 << 7)
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
static int changed_options;
static double csq_delay = 10;
static double cnti_delay = 10;
static double creg_delay = 10;
static double cgreg_delay = 10;
static double cops_delay = 60;
/* raw rssi & ber values, 99 equals 'no value' */
static int saved_rssi = 99, saved_ber = 99;
static char *saved_op;
static char *saved_opid;
static char *saved_nt0;
static const char *saved_reg;
static const char *saved_greg;
static char *saved_iccid;
static char *saved_imsi;
static char *saved_number;
static char *saved_simop;
static char *saved_simopid;
static int my_copn = 0;
static int scan_ok;
static char *saved_brand;
static char *saved_model;
static char *saved_rev;

static void changed_brand(void);
static void changed_model(void);

/* command queue */
struct str {
	struct str *next;
	char a[1];
};

static struct str *strq, *strqlast;
/* count successive blocked writes */
static int nsuccessiveblocks;

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

/* operators */
struct operator {
	struct operator *next;
	char id[8];
	int idlen;
	char name[2];
};

static struct operator *operators;

static struct operator *imsi_to_operator(const char *imsi);
static inline struct operator *opid_to_operator(const char *id)
{
	/* this lookup is almost just the same as for imsi */
	return imsi_to_operator(id);
}

static struct operator *add_operator(const char *id, const char *name)
{
	int len;
	struct operator *op;

	/* avoid duplicates */
	op = opid_to_operator(id);
	if (op)
		return op;

	/* add new entry */
	len = strlen(name ?: "");
	op = malloc(sizeof(*op) + len);
	if (!op)
		mylog(LOG_ERR, "malloc %u: %s", sizeof(*op)+len, ESTR(errno));
	memset(op, 0, sizeof(*op));
	strncpy(op->id, id, sizeof(op->id));
	op->idlen = strlen(op->id);
	strcpy(op->name, name);

	/* add */
	op->next = operators;
	operators = op;
	/* ready */
	return op;
}

static void free_operators(void)
{
	struct operator *curr;

	for (; operators; ) {
		curr = operators;
		operators = curr->next;
		free(curr);
	}
}

static struct operator *imsi_to_operator(const char *imsi)
{
	struct operator *op;

	if (!imsi)
		return NULL;
	for (op = operators; op; op = op->next) {
		if (!strncmp(imsi, op->id, op->idlen))
			return op;
	}
	return NULL;
}

/* lists */
static const char *const cregstrs[] = {
	[0] = "none",
	[1] = "registered",
	[2] = "searching",
	[3] = "denied",
	[4] = "unknown",
	[5] = "roaming",
};

/* AT iface */
__attribute__((format(printf,1,2)))
static int at_write(const char *fmt, ...);
static int at_ifnotqueued(const char *atcmd);
/* low-level write */
static int at_ll_write(const char *str);

static void at_next_cmd(void *dat)
{
	if (strq) {
		if (at_ll_write(strq->a) < 0) {
			/* reschedule myself */
			libt_add_timeout(1, at_next_cmd, dat);
		}
	}
}

static void at_timeout(void *dat)
{
	mypublish("fail", valuetostr("%s: timeout", strq->a), 0);
	mylog(LOG_WARNING, "%s: timeout", strq->a);
	at_next_cmd(NULL);
}

static void publish_received_property(const char *mqttname, const char *str, char **pcache)
{
	if (strcmp(*pcache ?: "", str ?: "")) {
		myfree(*pcache);
		*pcache = (str && *str) ? strdup(str) : NULL;
		mypublish(mqttname, str, 1);

		if (pcache == &saved_brand)
			changed_brand();
		else if (pcache == &saved_model)
			changed_model();
	}
}
static char *strip_quotes(char *str)
{
	char *stre;

	if (str) {
		stre = str+strlen(str)-1;
		if (*str == '"' && *stre == '"') {
			*stre = 0;
			++str;
		}
	}
	return str;
}

static void at_recvd_info(char *str)
{
	if (!str) {

	} else if (!strncasecmp(str, "+cpin: ", 7)) {
		if (!strcasecmp(str+7, "ready")) {
			/* SIM card become ready */
			at_write("at+cspn?");
			at_write("at+ccid");
			at_write("at+cimi");
			at_write("at+cnum");
			if ((options & O_SIMCOM) &&
					(!strq || strcasecmp(strq->a, "at+cpin?")))
				/* for simcom modem, don't issue at+copn
				 * when +cpin arrives as URC (not in response of at+cpin?
				 */
				return;
issue_at_copn:
			at_write("at+copn");
			++my_copn;
		}
	} else if (!strcasecmp(str, "SMS DONE")) {
		/* resume at+copn */
		goto issue_at_copn;

	} else if (!strcasecmp(str, "+simcard: not available")) {
		/* SIM card lost */
		publish_received_property("number", "", &saved_number);
		publish_received_property("iccid", "", &saved_iccid);
		publish_received_property("imsi", "", &saved_imsi);
		publish_received_property("op", "", &saved_simop);
		publish_received_property("opid", "", &saved_simopid);
		publish_received_property("simop", "", &saved_simop);
		publish_received_property("simopid", "", &saved_simopid);
		mypublish("ops", "", 0);
		free_operators();

	} else if (!strncasecmp(str, "+cspn: ", 7)) {
		publish_received_property("simop", strip_quotes(strtok(str+7, ",")), &saved_simop);

	} else if (!strncasecmp(str, "+ccid: ", 7)) {
		publish_received_property("iccid", strip_quotes(str+7), &saved_iccid);

	} else if (!strncasecmp(str, "+cnum: ", 7)) {
		/* parse 'label,number,type' */
		strtok(str+7, ",");
		publish_received_property("number", strip_quotes(strtok(NULL, ",")), &saved_number);

	} else if (!strncasecmp(str, "+creg: ", 7)) {
		/* find value a from a or n,a */
		str = strtok(str+7, ",");
		/* try 2nd value, or take 1st */
		str = strtok(NULL, ",") ?: str;

		int idx = strtoul(str, NULL, 10);

		if (idx >= sizeof(cregstrs)/sizeof(cregstrs[0]))
			idx = 4;
		if (cregstrs[idx] != saved_reg) {
			saved_reg = cregstrs[idx];
			mypublish("reg", saved_reg, 1);
			if (idx == 1 || idx == 3 || idx == 5)
				at_write("at+cops?");
			else {
				publish_received_property("op", "", &saved_op);
				publish_received_property("opid", "", &saved_op);
			}
		}
	} else if (!strncasecmp(str, "+cgreg: ", 8)) {
		/* find value a from a or n,a */
		str = strtok(str+8, ",");
		/* try 2nd value, or take 1st */
		str = strtok(NULL, ",") ?: str;

		int idx = strtoul(str, NULL, 10);

		if (idx >= sizeof(cregstrs)/sizeof(cregstrs[0]))
			idx = 4;
		if (cregstrs[idx] != saved_greg) {
			saved_reg = cregstrs[idx];
			mypublish("greg", saved_greg, 1);
		}
	} else if (!strncasecmp(str, "+csq: ", 6)) {
		int rssi, ber;
		char *endp;

		/* response[1] is of format: '+CSQ: <RSSI>,<BER>' */
		if (strncasecmp(str, "+CSQ: ", 6))
			return;
		rssi = strtoul(str+6, &endp, 0);
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

	} else if (!strncasecmp(str, "*cnti: 0,", 9)) {
		publish_received_property("nt", str+9, &saved_nt0);

	} else if (!strncasecmp(str, "+cops: ", 7)) {
		if (str[7] == '(') {
			/* at+cops=? : return list of operators */
			static char buf[1024*16];
			char *pbuf, *endp;
			char *name, *id;
			int stat;

			pbuf = buf;
			for (str += 7; *str == '('; str = endp ?: "") {
				++str;
				endp = strstr(str, "),");
				if (endp) {
					*endp = 0;
					endp += 2;
				}
				/* parse operator */
				stat = strtoul(strtok(str, ",\""), NULL, 0);
				name = strip_quotes(strtok(NULL, ","));
				strtok(NULL, ",");
				id = strip_quotes(strtok(NULL, ","));

				/* append operator to txbuf */
				pbuf += sprintf(pbuf, "%s%c%s:%s", (pbuf > buf) ? "," : "",
						(stat < 4) ? "? *-"[stat] : '?',
						id, name);
			}
			mypublish("ops", buf, 0);
			scan_ok = 1;
		} else {
			/* at+cops? : return current operator */
			/* mode,format,"operator",tech */
			strtok(str+7, ",");
			strtok(NULL, ",");
			publish_received_property("opid", strip_quotes(strtok(NULL, ",")), &saved_opid);

			struct operator *op = opid_to_operator(saved_opid);
			if (op)
				publish_received_property("op", op->name, &saved_op);
		}
	} else if (!strncasecmp(str, "+copn: ", 7)) {
		char *num, *name;
		struct operator *op;

		num = strip_quotes(strtok(str+7, ","));
		name = strip_quotes(strtok(NULL, ","));
		op = add_operator(num, name);
		if (!saved_simopid && saved_imsi && op && !strncmp(saved_imsi, op->id, op->idlen)) {
			/* publish sim operator */
			publish_received_property("simopid", op->id, &saved_simopid);
			if (!saved_simop)
				/* only publish if at+cspn didn't produce any result */
				publish_received_property("simop", op->name, &saved_simop);
		}
		if (saved_opid && !saved_op && op && !strcmp(saved_opid, op->id))
			/* publish operator name */
			publish_received_property("op", op->name, &saved_op);

	} else if (!strncasecmp(str, "+cgmi: ", 7)) {
		publish_received_property("brand", strip_quotes(strtok(str+7, ",")), &saved_brand);
	} else if (!strncasecmp(str, "+cgmm: ", 7)) {
		publish_received_property("model", strip_quotes(strtok(str+7, ",")), &saved_model);
	} else if (!strncasecmp(str, "+cgmr: ", 7)) {
		publish_received_property("rev", strip_quotes(strtok(str+7, ",")), &saved_rev);

	}
}

static void at_recvd_response(int argc, char *argv[])
{
	if (strncasecmp(argv[0], "at", 2)) {
		/* not an AT command feedback */
		return;
	/* regular commands ... */
	} else if (strcmp(argv[argc-1], "OK")) {
		mypublish("fail", valuetostr("%s: %s", argv[0], argv[argc-1]), 0);
		mylog(LOG_WARNING, "Command '%s': %s", argv[0], argv[argc-1]);

	} else if (!strcasecmp(argv[0], "at+cimi")) {
		const struct operator *op;

		publish_received_property("imsi", strip_quotes(argv[1]), &saved_imsi);
		op = imsi_to_operator(saved_imsi);
		if (op) {
			publish_received_property("simop", op->name, &saved_simop);
			if (!saved_simopid)
				/* only publish if at+cspn didn't produce any result */
				publish_received_property("simopid", op->id, &saved_simopid);
		}

	} else if (!strcasecmp(argv[0], "at+copn")) {
		/* stop blocking copn info */
		if (--my_copn < 0)
			my_copn = 0;
		if (saved_imsi && !saved_simopid) {
			/* operator not found in list :-(,
			 * take 5 characters from IMSI
			 */
			char simopid[8] = {};

			strncpy(simopid, saved_imsi, 5);
			publish_received_property("simopid", simopid, &saved_simopid);
		}
	} else if (!strcasecmp(argv[0], "at+cops=?")) {
		/* scan finalized without result */
		if (!scan_ok)
			mypublish("ops", "", 0);

	} else if (!strcasecmp(argv[0], "at+cgmi")) {
		if (argc > 2)
			/* argv[1] is value */
			publish_received_property("brand", strip_quotes(argv[1]), &saved_brand);
	} else if (!strcasecmp(argv[0], "at+cgmm")) {
		if (argc > 2)
			/* argv[1] is value */
			publish_received_property("model", strip_quotes(argv[1]), &saved_model);
	} else if (!strcasecmp(argv[0], "at+cgmr")) {
		if (argc > 2)
			/* argv[1] is value */
			publish_received_property("rev", strip_quotes(argv[1]), &saved_rev);
	}
}

static void at_recvd(char *line)
{
	char *str, *sep, *end;
	static char buf[1024*16], reconstructed[1024*16];
	static int consumed, fill;
#define NARGV 32
	static char *argv[NARGV];
	static int argc = 1;
	int len, j;

	len = strlen(line);
	if (fill+len+1 >= sizeof(buf) && consumed) {
		memmove(buf, buf+consumed, fill+1-consumed);
		/* adapt the strings in argv for the new position */
		for (j = 1; j < argc; ++j)
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
		/* strip leading/trailing \r */
		for (; *str == '\r'; ++str);
		end = str+strlen(str)-1;
		for (; end >= str && *end == '\r'; --end)
			*end = 0;

		consumed = sep ? sep - buf : fill;

		/* process */
		if (!*str)
			/* empty str */
			continue;
		if ((strchr("+*", *str) && strncmp(str, "+CME ERROR", 10)) ||
			!strcasecmp(str, "NO CARRIER") ||
			((options & O_SIMCOM) && !strcmp(str+strlen(str)-5, " DONE"))) {
			/* treat different */
			if (strncasecmp(str, "+copn: ", 7) || !my_copn)
				mypublish("raw/at", str, 0);
			at_recvd_info(str);
			continue;
		}
		/* collect response */
		argv[argc++] = str;
		if (!strcmp(str, "OK") ||
				!strncmp(str, "+CME ERROR", 10) ||
				!strcmp(str, "ABORT") ||
				!strcmp(str, "ERROR")) {
			int skip = strq ? 0 : 1;
			argv[0] = strq ? strq->a : "";
			/* reconstruct clean packet */
			for (str = reconstructed, j = skip; j < argc; ++j) {
				if (j > skip)
					*str++ = '\t';
				strcpy(str, argv[j]);
				str += strlen(str);
			}
			*str = 0;
			/* publish raw response */
			mypublish("raw/at", reconstructed, 0);

			/* process this command */
			if (ignore_responses > 0) {
				--ignore_responses;
			} else {
				argv[argc] = NULL;
				at_recvd_response(argc-skip, argv+skip);
			}
			/* restart response collection */
			argc = 1;
			/* queue admin */
			libt_remove_timeout(at_timeout, NULL);
			/* remove head from queue */
			free(pop_strq());
			/* issue next cmd to device */
			at_next_cmd(NULL);

		} else if (argc >= NARGV-1) {
			/* drop items */
			--argc;
			argv[argc-1] = "...";
		}
	}
	if (consumed >= fill && argc <= 1)
		consumed = fill = 0;
}

/* AT API */
static int at_ll_write(const char *str)
{
	struct iovec vec[2] = {
		[0] = { .iov_base = (void *)str, .iov_len = strlen(str), },
		[1] = { .iov_base = "\r", .iov_len = 1, },
	};
	int ret;

	ret = writev(atsock, vec, 2);
	if (ret < 0 && errno == EAGAIN) {
		/* allow this */
		if (++nsuccessiveblocks > 10) {
			mypublish("fail", valuetostr("writev %7s: %i x %s", str, nsuccessiveblocks, ESTR(EAGAIN)), 0);
			mylog(LOG_ERR, "writev %s %s: %i x %s", atdev, str, nsuccessiveblocks, ESTR(EAGAIN));
		}
	} else if (ret < 0) {
		ret = errno;
		mypublish("fail", valuetostr("writev %7s: %s", str, ESTR(ret)), 0);
		mylog(LOG_ERR, "writev %s %7s: %s", atdev, str, ESTR(ret));
	} else if (ret < vec[0].iov_len+vec[1].iov_len) {
		mypublish("fail", valuetostr("writev %7s: incomplete", str), 0);
		mylog(LOG_ERR, "writev %s %7s: incomplete %u/%u", atdev, str, ret, vec[0].iov_len+vec[1].iov_len);
	} else {
		double timeout = 5;
		nsuccessiveblocks = 0;
		if (!strcasecmp(str, "at+cops=?")) {
			scan_ok = 0;
			timeout = 180;
		} else if (!strncasecmp(str, "at+cops=", 8))
			/* operator scan takes time */
			timeout = 60;
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

	/* add to queue */
	add_strq(buf);
	if (!strq->next) {
		/* this is first element in the queue,
		 * write immediately */
		if (at_ll_write(strq->a) < 0)
			/* schedule repeat */
			libt_add_timeout(1, at_next_cmd, NULL);
	}
	return 0;
}

static int at_ifnotqueued(const char *atcmd)
{
	struct str *str;

	for (str = strq; str; str = str->next) {
		if (!strcmp(atcmd, str->a))
			return 0;
	}
	/* queue a new entry */
	at_write("%s", atcmd);
	return 1;
}

static void at_creg(void *dat)
{
	at_ifnotqueued("at+creg?");
	/* repeat */
	libt_add_timeout(creg_delay, at_creg, dat);
}

static void at_cgreg(void *dat)
{
	at_ifnotqueued("at+cgreg?");
	/* repeat */
	libt_add_timeout(cgreg_delay, at_cgreg, dat);
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
	libt_add_timeout(cops_delay, at_cops, dat);
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

	if (!strcmp(msg->topic+mqtt_prefix_len, "raw/send"))
		at_write("%s", (char *)msg->payload);

	else if (!strcmp(msg->topic+mqtt_prefix_len, "ops/scan")) {
		if (options & O_DETACHEDSCAN)
			at_write("%s", "at+cops=2");
		at_write("at+cops=?");
	}
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
			changed_options |= opt;
			switch (opt) {
			case O_CSQ:
				if (optarg)
					csq_delay = strtod(optarg, NULL);
				break;
			case O_CNTI:
				if (optarg)
					cnti_delay = strtod(optarg, NULL);
				break;
			case O_CREG:
				if (optarg)
					creg_delay = strtod(optarg, NULL);
				break;
			case O_CGREG:
				if (optarg)
					cgreg_delay = strtod(optarg, NULL);
				break;
			case O_COPS:
				if (optarg)
					cops_delay = strtod(optarg, NULL);
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
	cfmakeraw(&tio);
	if (tcsetattr(atsock, TCSANOW, &tio) < 0)
		mylog(LOG_ERR, "tcsetattr %s failed: %s", atdev, ESTR(errno));
	tcflush(atsock, TCIOFLUSH);

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
	subscribe_topic("%sraw/send", mqtt_prefix);
	subscribe_topic("%sops/scan", mqtt_prefix);

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
	at_write("ate0");
	at_write("at+cpin?");
	if (options & O_CREG)
		at_creg(NULL);
	else
		at_write("at+creg?");
	if (options & O_CGREG)
		at_cgreg(NULL);
	else
		at_write("at+cgreg?");
	if (options & O_CSQ)
		at_csq(NULL);
	else if (options & O_AUTOCSQ) {
		at_write("at+autocsq=1,1");
		at_write("at+csqdelta=1");
	} else
		at_write("at+csq");
	if (options & O_CNTI)
		at_cnti(NULL);
	/* set alphanumeric operator names */
	at_write("at+cops=3,2");
	if (options & O_COPS)
		at_cops(NULL);
	else
		at_write("at+cops?");

	/* device info */
	at_write("at+cgmi");
	at_write("at+cgmm");
	at_write("at+cgmr");

	/* clear potentially retained values in the broker */
	mypublish("rssi", NULL, 1);
	mypublish("ber", NULL, 1);
	mypublish("op", NULL, 1);
	mypublish("opid", NULL, 1);
	mypublish("nt", NULL, 1);
	mypublish("reg", NULL, 1);
	mypublish("greg", NULL, 1);
	mypublish("imsi", NULL, 1);
	mypublish("iccid", NULL, 1);
	mypublish("number", NULL, 1);
	mypublish("simop", NULL, 1);
	mypublish("simopid", NULL, 1);
	mypublish("brand", NULL, 1);
	mypublish("model", NULL, 1);
	mypublish("rev", NULL, 1);
	/* make sure to remove any retained scan results, set retained */
	mypublish("ops", "", 1);

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
	if (saved_opid)
		mypublish("opid", NULL, 1);
	if (saved_nt0)
		mypublish("nt", NULL, 1);
	if (saved_reg)
		mypublish("reg", NULL, 1);
	if (saved_greg)
		mypublish("greg", NULL, 1);
	if (saved_imsi)
		mypublish("imsi", NULL, 1);
	if (saved_iccid)
		mypublish("iccid", NULL, 1);
	if (saved_number)
		mypublish("number", NULL, 1);
	if (saved_simop)
		mypublish("simop", NULL, 1);
	if (saved_simopid)
		mypublish("simopid", NULL, 1);
	if (saved_brand)
		mypublish("brand", NULL, 1);
	if (saved_model)
		mypublish("model", NULL, 1);
	if (saved_rev)
		mypublish("rev", NULL, 1);
	mypublish("ops", "", 0);

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

struct quirck {
	int option;
	const char *needle;
	const char *desc;
};

static void test_quircks(const char *haystack, const struct quirck *q)
{
	for (; q->desc; ++q) {
		if (changed_options & q->option)
			/* changed in program options */
			continue;
		if (strstr(haystack, q->needle)) {
			if (!(options & q->option)) {
				options |= q->option;
				mylog(LOG_WARNING, "enabled %s", q->desc);
			}
		} else if (options & q->option) {
			options &= ~q->option;
			mylog(LOG_WARNING, "disabled %s", q->desc);
		}
	}
}

static struct quirck brand_quircks[] = {
	{ O_SIMCOM, "SIMCOM", "simcom", },
	{},
};
static void changed_brand(void)
{
	test_quircks(saved_brand ?: "", brand_quircks);
}

static struct quirck model_quircks[] = {
	{ O_DETACHEDSCAN, "SIM75", "detached scan", },
	{},
};

static void changed_model(void)
{
	test_quircks(saved_model ?: "", model_quircks);
}
