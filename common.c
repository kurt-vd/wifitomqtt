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
void mylog(int loglevel, const char *fmt, ...)
{
	static int use_stderr = -1;
	va_list va;

	if (use_stderr < 0) {
		char *tty;

		tty = ttyname(STDERR_FILENO);
		use_stderr = tty && !!strcmp(tty, "/dev/console");
	}

	va_start(va, fmt);
	if (use_stderr) {
		vfprintf(stderr, fmt, va);
		fputc('\n', stderr);
		fflush(stderr);
	} else
		vsyslog(loglevel, fmt, va);
	va_end(va);
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
	if (ret < 0)
		mylog(LOG_ERR, "mosquitto_publish %s: %s", selfsynctopic, mosquitto_strerror(ret));
}

int is_self_sync(const struct mosquitto_message *msg)
{
	return !strcmp(msg->topic, selfsynctopic) &&
		!strcmp(myuuid, msg->payload ?: "");
}
