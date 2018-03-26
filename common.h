#ifndef _common_h_
#define _common_h_
#ifdef __cplusplus
extern "C" {
#endif

/* forward struct declarations */
struct mosquitto;
struct mosquitto_message;

/* what's in common.c ? */

/* generic error logging */
#define ESTR(num)	strerror(num)
__attribute__((format(printf,2,3)))
extern void mylog(int loglevel, const char *fmt, ...);

/* MQTT self-sync */
extern void send_self_sync(struct mosquitto *, int qos);
extern int is_self_sync(const struct mosquitto_message *);

#ifdef __cplusplus
}
#endif
#endif
