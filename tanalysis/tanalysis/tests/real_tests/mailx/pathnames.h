/*	$OpenBSD: pathnames.h,v 1.7 2003/06/03 02:56:11 millert Exp $	*/
/*	$NetBSD: pathnames.h,v 1.4 1996/06/08 19:48:34 christos Exp $	*/

/*
 * Copyright (c) 1989, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)pathnames.h	8.1 (Berkeley) 6/6/93
 *	$NetBSD: pathnames.h,v 1.4 1996/06/08 19:48:34 christos Exp $
 */


/* executables */
#ifndef _PATH_SHELL
#define _PATH_SHELL	"/bin/sh"
#endif
#ifndef _PATH_PAGER
#define _PATH_PAGER	"/usr/bin/pager"
#endif
#ifndef _PATH_EX
#define _PATH_EX	"/usr/bin/editor"
#endif
#ifndef _PATH_VI
#define _PATH_VI	"/usr/bin/vi"
#endif
#ifndef _PATH_SENDMAIL
#define _PATH_SENDMAIL	"/usr/sbin/sendmail"
#endif

/* directories */
#ifndef _PATH_TMP
#define _PATH_TMP	"/tmp/"
#endif

/* executables */
#ifndef _PATH_LS
#define _PATH_LS	"/bin/ls"
#endif

#ifndef DEBIAN
#define _PATH_EX	"/usr/bin/ex"
#define _PATH_MORE	"/usr/bin/more"
#define _PATH_LOCKSPOOL	"/usr/libexec/lockspool"
#endif

/* mail runtime files */
#ifndef _PATH_MAILDIR
#define _PATH_MAILDIR	"/var/mail"
#endif

/* directories & files */
#define _PATH_HELP	"/usr/share/bsd-mailx/mail.help"
#define _PATH_TILDE	"/usr/share/bsd-mailx/mail.tildehelp"
#define _PATH_MASTER_RC	"/etc/mail.rc"
#define _PATH_LOCTMP	"/tmp/local.XXXXXXXXXX"
