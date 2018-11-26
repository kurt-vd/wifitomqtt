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
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <unistd.h>
#include <getopt.h>
#include <fcntl.h>
#include <poll.h>
#include <termios.h>
#include <syslog.h>

#include "common.h"

#define NAME "attest"
#ifndef VERSION
#define VERSION "<undefined version>"
#endif

#define ESTR(num)	strerror(num)

/* program options */
static const char help_msg[] =
	NAME ": test AT command for modem port\n"
	"usage:	" NAME " [OPTIONS ...] DEVICE [RESPONSE ...]\n"
	"\n"
	"Options\n"
	" -V, --version		Show version\n"
	" -v, --verbose		Be more verbose\n"
	"\n"
	"Arguments\n"
	" DEVICE	TTY device for modem\n"
	;

#ifdef _GNU_SOURCE
static struct option long_opts[] = {
	{ "help", no_argument, NULL, '?', },
	{ "version", no_argument, NULL, 'V', },
	{ "verbose", no_argument, NULL, 'v', },
	{ },
};
#else
#define getopt_long(argc, argv, optstring, longopts, longindex) \
	getopt((argc), (argv), (optstring))
#endif
static const char optstring[] = "Vv?";

/* logging */
static int loglevel = LOG_WARNING;

/* AT */
static const char *atdev;
static int atsock;

/* signal handler */
static void onsigalrm(int signr)
{
	mylog(LOG_ERR, "attest %s failed by timeout", atdev);
}

static const char *const default_needles[] = {
	"OK",
	//"ERROR",
	//"NO CARRIER",
	NULL,
};

static char buf[1024];

int main(int argc, char *argv[])
{
	int opt, ret;
	char *str, *next;
	const char *const *needles, *const *np;

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
	atdev = argv[optind++];
	needles = (optind < argc) ? (const char **)argv+optind : default_needles;

	/* install signal handler before opening the port,
	 * bad devices may hang already there
	 */
	signal(SIGALRM, onsigalrm);
	/* set timeout to 10 seconds */
	alarm(10);

	/* AT */
	atsock = open(atdev, O_RDWR | O_NOCTTY | O_CLOEXEC);
	if (atsock < 0)
		mylog(LOG_ERR, "open %s: %s", atdev, ESTR(errno));

	struct termios tio;
	if (tcgetattr(atsock, &tio) < 0)
		mylog(LOG_ERR, "tcgetattr %s failed: %s", atdev, ESTR(errno));
	cfmakeraw(&tio);
	if (tcsetattr(atsock, TCSANOW, &tio) < 0)
		mylog(LOG_ERR, "tcsetattr %s failed: %s", atdev, ESTR(errno));

	/* step 1: push \r to finalize any pending garbage */
	ret = write(atsock, "\r", 1);
	if (ret <= 0)
		mylog(LOG_ERR, "write %s '\\r': %s", atdev, ret ? ESTR(errno) : "EOF");
	/* wait using poll to avoid interference with SIGARLM */
	poll(NULL, 0, 1000);
	/* remove garbage */
	tcflush(atsock, TCIOFLUSH);

	/* step 2: push AT\r and wait for OK
	 * we expect OK to fit in the first 1024 bytes,
	 * since we just flushed the input queue
	 * Hence, we read only once from the port
	 */
	ret = write(atsock, "AT\r", 3);
	if (ret < 3)
		mylog(LOG_ERR, "write %s 'AT\\r': %s", atdev, (ret < 0) ? ESTR(errno) : "EOF");

	int fill = 0, consumed = 0;
	for (;;) {
		if (consumed < fill)
			memmove(buf, buf+consumed, fill-consumed+1);
		else
			fill = consumed = 0;
		ret = read(atsock, buf+fill, sizeof(buf)-1-fill);
		if (ret <= 0)
			mylog(LOG_ERR, "read %s: %s", atdev, ret ? ESTR(errno) : "EOF");
		fill += ret;
		buf[fill] = 0;

		/* parse reply in lines */
		for (str = buf; *str; str = next) {
			next = strpbrk(str, "\n\r");
			if (!next)
				break;
			for (; *next && strchr("\n\r", *next); ++next)
				*next = 0;
			if (!*str)
				/* skip empty strings */
				continue;
			mylog(LOG_INFO, "%s got '%s'", atdev, str);
			for (np = needles; *np; ++np)
				if (!strcmp(str, *np))
					return 0;
		}
		consumed = str-buf;
	}
	mylog(LOG_WARNING, "%s answered not OK", atdev);
	return 1;
}
