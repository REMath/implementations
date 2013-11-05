#	$OpenBSD: Makefile,v 1.8 1997/09/21 11:49:50 deraadt Exp $

PROG=mail
CC=gcc

CFLAGS=-D_BSD_SOURCE -DDEBIAN -g -Wall -IEXT

ifneq (,$(findstring noopt,$(DEB_BUILD_OPTIONS)))
  CFLAGS += -O0
else
  CFLAGS += -O2
endif

SRCS=	version.c _aux.c cmd1.c cmd2.c cmd3.c cmdtab.c collect.c \
	edit.c fio.c getname.c head.c v7.local.c lex.c list.c main.c names.c \
	popen.c quit.c send.c strings.c temp.c tty.c vars.c \
	EXT/strlcat.c EXT/strlcpy.c EXT/vis.c

OBJS=$(SRCS:%.c=%.o)
LIBS=-llockfile

SFILES=	mail.help mail.tildehelp
EFILES=	mail.rc
MFILES=	mail.1

all: $(PROG)

beforeinstall:
	cd ${.CURDIR}/misc; ${INSTALL} ${INSTALL_COPY} -o ${BINOWN} -g ${BINGRP} \
	    -m 444 ${SFILES} ${DESTDIR}/usr/share/misc

distribution:
	cd ${.CURDIR}/misc; ${INSTALL} ${INSTALL_COPY} -o root -g wheel \
	    -m 644 ${EFILES} ${DESTDIR}/etc


 
$(PROG): $(OBJS)
	$(CC) $(LDFLAGS) -o $@ $(OBJS) $(LIBS)
 
.c.o:
	$(CC) $(CFLAGS) -c $< -o $@
 
.y.c:
	bison $<
	mv -f $*.tab.c $@
 
clean:
	rm -f $(PROG) $(OBJS) *~ core
 
install:
	install -p -c -m 755 $(PROG) $(DESTDIR)/usr/bin/bsd-mailx
	install -p -c -m 644 $(MFILES) $(DESTDIR)/usr/share/man/man1/bsd-mailx.1
	cd misc && install -p -c -m 644 $(EFILES) $(DESTDIR)/etc/
	cd misc && install -p -c -m 644 $(SFILES) $(DESTDIR)/usr/share/bsd-mailx/
