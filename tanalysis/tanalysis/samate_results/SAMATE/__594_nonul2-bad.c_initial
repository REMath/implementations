/*
Description: A read generates a string that may not have NUL termination.  Copying the string can cause a stack buffer to be overrun.
Keywords: Unix C Size0 Complex0 BufferOverflow Stack Read NoNul
ValidStream: "a"*20
InvalidStream: "a"*100

Copyright 2005 Fortify Software.

Permission is hereby granted, without written agreement or royalty fee, to
use, copy, modify, and distribute this software and its documentation for
any purpose, provided that the above copyright notice and the following
three paragraphs appear in all copies of this software.

IN NO EVENT SHALL FORTIFY SOFTWARE BE LIABLE TO ANY PARTY FOR DIRECT,
INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE
USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF FORTIFY SOFTWARE HAS
BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMANGE.

FORTIFY SOFTWARE SPECIFICALLY DISCLAIMS ANY WARRANTIES INCLUDING, BUT NOT
LIMITED TO THE IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE, AND NON-INFRINGEMENT.

THE SOFTWARE IS PROVIDED ON AN "AS-IS" BASIS AND FORTIFY SOFTWARE HAS NO
OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
MODIFICATIONS.
*/

#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* 
 * we pick a round buffer size in hopes that the compiler lays these
 * out next to each other without padding.  Other layouts may
 * inadvertantly NUL terminate the buffer with stack garbage.
 */
#define	MAXSIZE		32

void
test(void)
{
	char buf2[MAXSIZE];
	char buf1[MAXSIZE];
	int n;

	/* read does not NUL terminate */
	n = read(0, buf1, sizeof buf1);	/* BAD */
	strcpy(buf2, buf1);				/* BAD */
	printf("result: %s\n", buf2);
}

int
main(int argc, char **argv)
{
	test();
	return 0;
}

