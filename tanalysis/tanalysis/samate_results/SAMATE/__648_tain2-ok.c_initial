/*
Description: Execl() is called with user-provided data but only if it matches an item in a safe list.
Keywords: Unix C Size0 Complex0 Taint Unsafe

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

char *validGames[] = {
	"moria", "fortune", "adventure", "zork", "rogue", "worm", "trek",
	0
};

#define	MAXSIZE		40
void
test(char *str)
{
	char buf[MAXSIZE];
	int x;

	/* str can contain ".." components */
	for(x = 0; validGames[x]; x++) {
		if(strcmp(str, validGames[x]) == 0)
			break;
	}
	if(!validGames[x])
		return;
	snprintf(buf, sizeof buf, "/usr/games/%s", str);
	buf[MAXSIZE-1] = 0;
	execl(buf, str, 0);			/* OK */
}

int
main(int argc, char **argv)
{
	char *userstr;

	if(argc > 1) {
		userstr = argv[1];
		test(userstr);
	}
	return 0;
}

