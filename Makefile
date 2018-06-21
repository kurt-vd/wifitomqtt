PROGS	= wifitomqtt ifaddrtomqtt
default	: $(PROGS)

PREFIX	= /usr/local

CC	= gcc
CFLAGS	= -Wall
CPPFLAGS= -D_GNU_SOURCE
LDLIBS	= -lmosquitto
INSTOPTS= -s

VERSION := $(shell git describe --tags --always)

-include config.mk

# avoid overruling the VERSION
CPPFLAGS += -DVERSION=\"$(VERSION)\"

ifneq (,$(findstring -DNOPLAINPSK, $(CPPFLAGS)))
wifitomqtt: LDLIBS+=-lcrypto
endif
wifitomqtt: libet/libt.o common.o

ifaddrtomqtt: libet/libt.o common.o

install: $(PROGS)
	$(foreach PROG, $(PROGS), install -vpD -m 0777 $(INSTOPTS) $(PROG) $(DESTDIR)$(PREFIX)/bin/$(PROG);)

clean:
	rm -rf $(wildcard *.o libet/*.o) $(PROGS)
