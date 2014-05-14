
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
$Header: /mnt/leo2/cvs/sabo/hist-040105/wu-ftpd/f2/call-realpath-bad.c,v 1.1.1.1 2004/01/05 17:27:49 tleek Exp $



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
$Header: /mnt/leo2/cvs/sabo/hist-040105/wu-ftpd/f2/call-realpath-bad.c,v 1.1.1.1 2004/01/05 17:27:49 tleek Exp $



*/


/*

<source>

*/

#include <stdio.h>
#include <string.h>
#include "my-include.h"
#include <assert.h>

char chroot_path[MAXPATHLEN];

/* Overflowing path[] can overwrite gid and uid and potentially escalate */
/* user privileges.  Also, the ret address of call_realpath can get overwritten*/
/* possibly leading to execution of arbitrary code */

/* call_realpath models the function makedir() inside ftpd.c which calls */
/* realpath() several times */

void call_realpath(char *name){

  unsigned int uid = 10;  
  unsigned int gid = 100;                 
  char path[MAXPATHLEN + 1];  /* for my-realpath() later  - cky */
  
  printf("Before my-realpath(): uid = %d, gid = %d\n", uid, gid);

  printf ("strlen(name) =%d\n", strlen(name));
  my_realpath(name, path, chroot_path);
  printf("Resolved path = %s\n", path);
  printf("After my-realpath(): uid = %d, gid = %d\n", uid, gid);
}

int main(int argc, char *argv[]){
  char *name;
  char *root_path;
  
  
  assert (argc==2 || argc==3);

  if (argc == 2){
    name = argv[1];      /* name could be very long, i.e longer than MAXPATHLEN*/
    root_path = "/";
  }
  else { // argc == 3 
    name = argv[1];      /* name could be very long, i.e longer than MAXPATHLEN*/
    root_path = argv[2];
  }
  
  (void) strncpy (chroot_path, root_path, sizeof (chroot_path));
  call_realpath(name);
  
  return 0;
} 


/*

</source>

*/

