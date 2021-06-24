#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <unistd.h>
#include <syslog.h>
#include <mosquitto.h>

#include "common.h"

/* error logging */
static int logtostderr = -1;
static int maxloglevel;

void setmyloglevel(int level)
{
	maxloglevel = level;
	if (!logtostderr)
		setlogmask(LOG_UPTO(level));
}
void setmylog(const char *name, int options, int facility, int level)
{
	char *tty;

	tty = ttyname(STDERR_FILENO);
	logtostderr = tty && !!strcmp(tty, "/dev/console");
	maxloglevel = level;
	if (!logtostderr && name) {
		openlog(name, options, facility);
		setlogmask(LOG_UPTO(level));
	} else {
		/* we append \n seperately.
		 * Make stderr line-buffered, so it results in 1 single write
		 */
		setlinebuf(stderr);
	}
}

void mylog(int loglevel, const char *fmt, ...)
{
	va_list va;

	if (logtostderr < 0)
		setmylog(NULL, 0, LOG_LOCAL1, LOG_WARNING);

	if (logtostderr && loglevel > maxloglevel)
		goto done;
	va_start(va, fmt);
	if (logtostderr) {
		vfprintf(stderr, fmt, va);
		fputc('\n', stderr);
		fflush(stderr);
	} else
		vsyslog(loglevel, fmt, va);
	va_end(va);
done:
	if (loglevel <= LOG_ERR)
		exit(1);
}

/* self-sync util */
static char myuuid[128];
static const char selfsynctopic[] = "tmp/selfsync";
void send_self_sync(struct mosquitto *mosq, int qos)
{
	int ret;

	sprintf(myuuid, "%i-%li-%i", getpid(), time(NULL), rand());

	ret = mosquitto_subscribe(mosq, NULL, selfsynctopic, qos);
	if (ret)
		mylog(LOG_ERR, "mosquitto_subscribe %s: %s", selfsynctopic, mosquitto_strerror(ret));
	ret = mosquitto_publish(mosq, NULL, selfsynctopic, strlen(myuuid), myuuid, qos, 0);
	if (ret)
		mylog(LOG_ERR, "mosquitto_publish %s: %s", selfsynctopic, mosquitto_strerror(ret));
}

int is_self_sync(const struct mosquitto_message *msg)
{
	return !strcmp(msg->topic, selfsynctopic) &&
		!strcmp(myuuid, msg->payload ?: "");
}
