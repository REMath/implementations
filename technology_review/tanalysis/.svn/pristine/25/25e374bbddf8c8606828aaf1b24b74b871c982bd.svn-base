
/*

MIT Copyright Notice

Copyright 2003 M.I.T.

Permission is hereby granted, without written agreement or royalty fee, to use, 
copy, modify, and distribute this software and its documentation for any 
purpose, provided that the above copyright notice and the following three 
paragraphs appear in all copies of this software.

IN NO EVENT SHALL M.I.T. BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, 
INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE 
AND ITS DOCUMENTATION, EVEN IF M.I.T. HAS BEEN ADVISED OF THE POSSIBILITY OF 
SUCH DAMANGE.

M.I.T. SPECIFICALLY DISCLAIMS ANY WARRANTIES INCLUDING, BUT NOT LIMITED TO 
THE IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, 
AND NON-INFRINGEMENT.

THE SOFTWARE IS PROVIDED ON AN "AS-IS" BASIS AND M.I.T. HAS NO OBLIGATION TO 
PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.

$Author: tleek $
$Date: 2004/01/05 17:27:49 $
$Header: /mnt/leo2/cvs/sabo/hist-040105/wu-ftpd/f2/realpath-2.4.2-ok.c,v 1.1.1.1 2004/01/05 17:27:49 tleek Exp $



*/


/*

WU-FTPD Copyright Notice


  Copyright (c) 1999,2000 WU-FTPD Development Group.  
  All rights reserved.
  
  Portions Copyright (c) 1980, 1985, 1988, 1989, 1990, 1991, 1993, 1994
    The Regents of the University of California.
  Portions Copyright (c) 1993, 1994 Washington University in Saint Louis.
  Portions Copyright (c) 1996, 1998 Berkeley Software Design, Inc.
  Portions Copyright (c) 1989 Massachusetts Institute of Technology.
  Portions Copyright (c) 1998 Sendmail, Inc.
  Portions Copyright (c) 1983, 1995, 1996, 1997 Eric P.  Allman.
  Portions Copyright (c) 1997 by Stan Barber.
  Portions Copyright (c) 1997 by Kent Landfield.
  Portions Copyright (c) 1991, 1992, 1993, 1994, 1995, 1996, 1997
    Free Software Foundation, Inc.  
 
  Use and distribution of this software and its source code are governed 
  by the terms and conditions of the WU-FTPD Software License ("LICENSE").
 
  If you did not receive a copy of the license, it may be obtained online
  at http://www.wu-ftpd.org/license.html.


$Author: tleek $
$Date: 2004/01/05 17:27:49 $
$Header: /mnt/leo2/cvs/sabo/hist-040105/wu-ftpd/f2/realpath-2.4.2-ok.c,v 1.1.1.1 2004/01/05 17:27:49 tleek Exp $



*/


/*

<source>

*/

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>


/* these three should be commented out for PolySpace */
#include <sys/types.h>
#include <signal.h>
#include <sys/signal.h>


#include <syslog.h>
#include "my-include.h"


#define HAVE_GETCWD 1

/*Comment out these lines for PolySpace */

#include <sys/stat.h>
#ifndef HAVE_SYMLINK
#define lstat stat
#endif


/* These two lines are needed for PolySpace */ 
/*
#define NSIG 64
#define S_IFLNK        0120000
*/

/*
  * delay_signaling(), enable_signaling - delay signal delivery for a while
  *
  * Author: Wietse Venema
  */


static sigset_t saved_sigmask;
static sigset_t block_sigmask;
static int delaying;
static int init_done;

/* init_mask - compute signal mask only once */

static void init_mask()
{
    int     sig;

    init_done = 1;
    sigemptyset(&block_sigmask);
    for (sig = 1; sig < NSIG; sig++)
	sigaddset(&block_sigmask, sig);
}

/* enable_signaling - deliver delayed signals and disable signal delay */

int     enable_signaling()
{
    if (delaying != 0) {
	delaying = 0;
	if (sigprocmask(SIG_SETMASK, &saved_sigmask, (sigset_t *) 0)<0) {
	  /*syslog(LOG_ERR, "sigprocmask: %m");*/ /* ISO doesn't support %m */
	    return (-1);
	}
    }
    return (0);
}

/* delay_signaling - save signal mask and block all signals */

int     delay_signaling()
{
    if (init_done == 0)
	init_mask();
    if (delaying == 0) {
	delaying = 1;
	if (sigprocmask(SIG_BLOCK, &block_sigmask, &saved_sigmask)<0) {
	  /* syslog(LOG_ERR, "sigprocmask: %m");*/
	    return (-1);
	}
    }
    return (0);
}

/* This is the function my-realpath that takes a non-canonicalized path and */
/* returns a canonicalized form in result */

char *my_realpath(const char *pathname, char *result, char* chroot_path){
  struct stat sbuf; 
  char canary[] = "GOOD";
  char curpath[MAXPATHLEN], workpath[MAXPATHLEN],linkpath[MAXPATHLEN], namebuf[MAXPATHLEN], *where, *ptr,*last;
  int len;
  uid_t userid;
  int resultcode;
  
  /* check arguments! */
  
  if (result == NULL)                    /* result must not be null! */
    return(NULL);
  
  if(pathname == NULL){            /* if pathname is null, there is nothing to do */
    *result = '\0'; 
    return(NULL);
  }
  
  printf("MY_REALPATH: pathname passed in = %s\n", pathname);
  

  /* OK */
  strncpy(curpath, pathname,MAXPATHLEN);
  printf ("canary=[%s]\n", canary);

  if (*pathname != '/') {
    uid_t userid;

   
#ifdef HAVE_GETCWD
    if (!getcwd(workpath,MAXPATHLEN)) {
#else
      if (!getwd(workpath)) {
#endif  
	userid = geteuid();
	delay_signaling(); /* we can't allow any signals while euid==0: kinch */
	seteuid(0);
#ifdef HAVE_GETCWD
	if (!getcwd(workpath,MAXPATHLEN)) {
#else
	  if (!getwd(workpath)) {
#endif
	    strncpy(result, ".", MAXPATHLEN+1);     
	    seteuid(userid);
	    enable_signaling();      /* we can allow signals once again: kinch */
	    return (NULL);
	  }
	  seteuid(userid);
	  enable_signaling();        /* we can allow signals once again: kinch */
	}
      } else
	*workpath = '\0';
      
  /* curpath is the path we're still resolving      */
  /* linkpath is the path a symbolic link points to */
  /* workpath is the path we've resolved            */
  
      /*MZ: Let's try to avoid the goto !!!!!!!!!! PolySpace can't handle it*/
      /* loop: */
      
      where = curpath;   /* where = pathname */
      
      while (*where != '\0') {
	if (!strcmp(where, ".")) {   
	  where++;
	  continue;
	}
	/* deal with "./" */
	if (!strncmp(where, "./", 2)) {
	  where += 2;
	  continue;
        }
	/* deal with "../" */
	if (!strncmp(where, "../", 3)) {
	  where += 3;
	  ptr = last = workpath;    /* workpath is cwd */
	  while (*ptr != '\0') {
	    if (*ptr == '/')
	      last = ptr;           /* finds the last slash in cwd */
	    ptr++;
	  }
	  *last = '\0';
	  continue;
	}
	ptr = strchr(where, '/');
	if (ptr == (char *)NULL)
	  ptr = where + strlen(where) - 1;
	else
	  *ptr = '\0';
	
	if (strlen(workpath) >= MAXPATHLEN){
	  return NULL;
	}
	else
	  strcpy(namebuf, workpath);         
	
	for (last = namebuf; *last; last++)
	  continue;
	if ((last == namebuf) || (*--last != '/')) {
	  /* OK */	  
	  strncat(namebuf, "/",MAXPATHLEN-strlen(namebuf)-1);
	  printf ("canary=[%s]\n", canary);
	}	
	/* OK */
	strncat(namebuf, where,MAXPATHLEN-strlen(namebuf)-1);
	printf ("canary=[%s]\n", canary);
	
	if (strlen(namebuf)+strlen(where)>=MAXPATHLEN) 
	  {
	    printf("BUFFER OVERFLOW ATTEMPTED...exiting\n");
	    return NULL;
	  }
	
	where = ++ptr;
	
	userid = geteuid();
	delay_signaling(); /* we can't allow any signals while euid==0: kinch */
	seteuid(0);
	resultcode = lstat(namebuf, &sbuf);
	seteuid(userid);
	enable_signaling(); /* we can allow signals once again: kinch */
	
	if (resultcode == -1) {
	  if (chroot_path == NULL){
	    if (strlen(namebuf) >= MAXPATHLEN) 
	      {
		printf("BUFFER OVERFLOW ATTEMPTED...exiting\n");
		return NULL;
	      }
	    else {
	      /* OK */
	      strcpy(result, namebuf);
	      printf ("canary=[%s]\n", canary);
	    }
	  }
	  else{
	    if (strlen(chroot_path) >= MAXPATHLEN){
	      printf("BUFFER OVERFLOW ATTEMPTED...exiting\n");
	      return NULL;
	    }
	    else{
	      /* OK */
	      strcpy(result, chroot_path);
	      printf ("canary=[%s]\n", canary);
	      
	      if (namebuf[0]!='/')
		{
		  if (strlen(namebuf) + strlen(result) > MAXPATHLEN){
		    printf("BUFFER OVERFLOW ATTEMPTED...exiting\n");
		    return NULL;
		  }
		  else {
		    /*OK*/
		    strcat(result, namebuf);
		    printf ("canary=[%s]\n", canary);

		  }
		}
	      else if (namebuf[1] != '\0') {
		for (ptr=result; *ptr!= '\0'; ptr++);
		if (ptr==result || *--ptr != '/')
		  {
		    if (strlen(namebuf) + strlen(result) > MAXPATHLEN)
		      {
			printf("BUFFER OVERFLOW ATTEMPTED...exiting\n");
			return NULL;
		      }
		    else {
		      /*OK*/
		      strcat(result, namebuf);
		      printf ("canary=[%s]\n", canary);
		    }
		  }
		else{
		  if (strlen(namebuf) + strlen(result) > MAXPATHLEN+1)
		    {
		      printf("BUFFER OVERFLOW ATTEMPTED...exiting\n");
		      return NULL;
		    }
		  else {
		    /*OK*/
		    strcat(result, &namebuf[1]);
		    printf ("canary=[%s]\n", canary);
		  }
		}
	      }
	    }
	  }
	  return (NULL);
	}
	
	/* was IFLNK */
#ifdef HAVE_SYMLINK
	if ((sbuf.st_mode & S_IFMT) == S_IFLNK) {
	  userid = geteuid();
	  delay_signaling(); /* we can't allow any signals while euid==0: kinch */
	  seteuid(0);
	  
	  len = readlink(namebuf, linkpath, MAXPATHLEN);   /* safe */
	  seteuid(userid);
	  enable_signaling(); /* we can allow signals once again: kinch */
	  if (len == 0) {
	    if (chroot_path == NULL)
	      {
		if (strlen(namebuf) > MAXPATHLEN){
		  printf("strlen(namebuf) > MAXPATHLEN\n");
		  return NULL;
		}
		else {
		  /* OK */
		  strcpy(result, namebuf);
		  printf ("canary=[%s]\n", canary);
		}
	      }
	    else {
	      
	      if (strlen(chroot_path) >= MAXPATHLEN)
		{
		  printf("strlen(chroot_path) >= MAXPATHLEN\n");
		  return NULL;
		}
	      else {
		/*OK*/
		strcpy(result, chroot_path);  
		printf ("canary=[%s]\n", canary);
  
	      }
	      if (namebuf[0]!='/')
		{
		  if (strlen(namebuf) + strlen(result) > MAXPATHLEN)
		    return NULL;
		  else {
		    /* OK */
		    strcat(result, namebuf);
		    printf ("canary=[%s]\n", canary);

		  }
		}
	      else if (namebuf[1]!='\0') {
		for (ptr=result; *ptr!= '\0'; ptr++);
		if (ptr==result || *--ptr != '/')
		  {
		    if (strlen(namebuf) + strlen(result) > MAXPATHLEN)
		      return NULL;
		    else {
		      /* OK */
		      strcat(result, namebuf);
		      printf ("canary=[%s]\n", canary);
		    }
		  }
		else
		  {
		    if (strlen(namebuf) + strlen(result) > MAXPATHLEN + 1)
		      return NULL;
		    else {
		      /* OK */
		      strcat(result, &namebuf[1]);
		      printf ("canary=[%s]\n", canary);
		    }
		  }
	      }
	    }
	    return (NULL);
	  }
	  *(linkpath + len) = '\0';   /* readlink doesn't null-terminate
				       * result */
	  if (*linkpath == '/')
	    *workpath = '\0';
	  if (*where) {
	    /* OK */
	    strncat(linkpath, "/",MAXPATHLEN-strlen(linkpath)-1);
	    printf ("canary=[%s]\n", canary);
	    
	    if (strlen(linkpath)+strlen(where)>=MAXPATHLEN) 
	      {
		printf("BUFFER OVERFLOW ATTEMPTED.. exiting\n");
		return NULL;
	      }
	    
	    /* OK */
	    strncat(linkpath, where, MAXPATHLEN-strlen(linkpath)- 1);
	    printf ("canary=[%s]\n", canary);
	  }
	  
	  if (strlen(linkpath) >= MAXPATHLEN)
	    {
	      printf("strlen(linkpath) >= MAXPATHLEN! Exiting..\n");
	      return NULL;
	    }
	  
	  /*OK*/
	  strcpy(curpath, linkpath);
	  printf ("canary=[%s]\n", canary);
	  
	  /*
	    Foggetaboutit...don't use a goto!
	    goto loop;  
	  */
	    /* These two lines accomplish the same thing as 'goto loop'*/
	     where = curpath;
	     continue;

	  }
#endif
	if ((sbuf.st_mode & S_IFDIR) == S_IFDIR) {
	  
	  if (strlen(namebuf) >= sizeof(workpath))
	    {
	      printf("strlen(namebuf) >= sizeof(workpath)\n");
	      return NULL;
	    }
	  else {
	    /*OK*/
	    strcpy(workpath, namebuf);
	    printf ("canary=[%s]\n", canary);
	  }	  
	  continue;
	}
	
	if (*where) {
	  if (chroot_path == NULL)
	    {
	      if (strlen(namebuf) >= MAXPATHLEN){
		printf("strlen(namebuf) > MAXPATHLEN\n");
		return NULL;
	      }
	      /*OK*/
	      strcpy(result, namebuf);
	      printf ("canary=[%s]\n", canary);
	    }
	  else {
	    
	    if (strlen(chroot_path) >= MAXPATHLEN){
	      printf("strlen(chroot_path) > MAXPATHLEN\n");
	      return NULL;
	    }
	    
	    strcpy(result, chroot_path);
	    
	    if (namebuf[0]!='/')
	      {
		if (strlen(namebuf) + strlen(result) > MAXPATHLEN)
		  {
		    printf("strlen(namebuf) + strlen(result) > MAXPATHLEN\n");
		    return NULL;
		  }
		
		/* OK */
		strcat(result, namebuf);
		printf ("canary=[%s]\n", canary);
	      }
	      else if (namebuf[1]!='\0') {
		for (ptr=result; *ptr!= '\0'; ptr++);
		if (ptr==result || *--ptr != '/')
		  {
		    if (strlen(namebuf) + strlen(result) > MAXPATHLEN)
		      {
			printf("strlen(namebuf) + strlen(result) > MAXPATHLEN\n");
			return NULL;
		      }
		    
		    /* OK */
		    strcat(result, namebuf);
		    printf ("canary=[%s]\n", canary);
		  }
		else
		  {
		  if (strlen(namebuf) + strlen(result) > MAXPATHLEN + 1)
		    {
		      printf("strlen(namebuf) + strlen(result) > MAXPATHLEN + 1\n"); 
		      return NULL;
		    }
		  
		  /* OK */
		  strcat(result, &namebuf[1]);
		  printf ("canary=[%s]\n", canary);
		  }
	      }
	  }
	  
	  return (NULL);      /* path/notadir/morepath */
	}  
	else{
	  if (strlen(namebuf) >= sizeof(workpath))
	    {
	      printf("strlen(namebuf) >= sizeof(workpath)\n");
	      return NULL;
	    }
	  
	  /* OK */
	  strcpy(workpath, namebuf);
	  printf ("canary=[%s]\n", canary);
	}
      }
      
      if (chroot_path == NULL){
	if (strlen(workpath) >= MAXPATHLEN){
	  printf("strlen(workpath) > MAXPATHLEN!\n");
	  return NULL;
	}
	
	/* OK */
	strcpy(result, workpath);
	printf ("canary=[%s]\n", canary);
      }
      else {
	if (strlen(chroot_path) >= MAXPATHLEN){
	  printf("strlen(chroot_path) >= MAXPATHLEN\n");
	  return NULL;
	}
	  /*OK*/
	strcpy(result, chroot_path);
	printf ("canary=[%s]\n", canary);
	
	if (workpath[0]!='/')
	  {
	    if (strlen(workpath) + strlen(result) > MAXPATHLEN)
	      {
		printf("strlen(workpath) + strlen(result) > MAXPATHLEN\n");
		return NULL;
	      }
	    /* OK */
	    strcat(result, workpath);
	    printf ("canary=[%s]\n", canary);
	  }
	else if (workpath[1] != '\0') {
	  for (ptr=result; *ptr!= '\0'; ptr++);
	  if (ptr==result || *--ptr != '/')
	    {
	      if (strlen(workpath) + strlen(result) > MAXPATHLEN)
		{
		  printf("strlen(workpath) + strlen(result) > MAXPATHLEN\n");
		  return NULL;
		}
	      /* OK */
	      strcat(result, workpath);
	      printf ("canary=[%s]\n", canary);
	    }
	  else{
	    if (strlen(workpath) + strlen(result) > MAXPATHLEN+1)
	      {
		printf("strlen(workpath) + strlen(result) > MAXPATHLEN + 1\n");
		return NULL;
	      }
	    /* OK */
	    strcat(result, &workpath[1]);
	    printf ("canary=[%s]\n", canary);
	  }
	}
      }
      return (result);
      
    }
    
    

    
    
   
    














/*

</source>

*/

