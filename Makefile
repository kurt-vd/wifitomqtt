PROGS	= wifitomqtt
PROGS	+= attomqtt
PROGS	+= atinsert
PROGS	+= attest
PROGS	+= ifaddrtomqtt
default	: $(PROGS)

PREFIX	= /usr/local

CC	= gcc
CFLAGS	= -Wall
CPPFLAGS= -D_GNU_SOURCE
LDLIBS	= -lmosquitto
INSTOPTS= -s

VERSION := $(shell git describe --tags --always)

-include config.mk

# common.c contains references to libmosquitto
# allow to not link those at all, while using
# other part
CFLAGS += -ffunction-sections -fdata-sections
LDFLAGS += -Wl,--gc-sections

# avoid overruling the VERSION
CPPFLAGS += -DVERSION=\"$(VERSION)\"

ifneq (,$(findstring -DNOPLAINPSK, $(CPPFLAGS)))
wifitomqtt: LDLIBS+=-lcrypto
endif
wifitomqtt: libet/libt.o common.o

attomqtt: libet/libt.o common.o

# attest is a small tiny program, remove mosquitto dependency
attest: LDLIBS:=$(subst -lmosquitto,,$(LDLIBS))
attest: common.o

ifaddrtomqtt: libet/libt.o common.o

install: $(PROGS)
	$(foreach PROG, $(PROGS), install -vpD -m 0777 $(INSTOPTS) $(PROG) $(DESTDIR)$(PREFIX)/bin/$(PROG);)

clean:
	rm -rf $(wildcard *.o libet/*.o) $(PROGS)
