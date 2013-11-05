/* This software was developed at the National Institute of Standards and
 * Technology by employees of the Federal Government in the course of their
 * official duties. Pursuant to title 17 Section 105 of the United States
 * Code this software is not subject to copyright protection and is in the
 * public domain. NIST assumes no responsibility whatsoever for its use by
 * other parties, and makes no guarantees, expressed or implied, about its
 * quality, reliability, or any other characteristic.

 * We would appreciate acknowledgement if the software is used.
 * The SAMATE project website is: http://samate.nist.gov
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

static unsigned short userID = 0;



char *getDefaultPassword() {
	char pass[256];
	// get the system password or do a query etc.
	return pass;
}


int main(int argc, char *argv[])
{
	const char passwords[2][255] = {"",""};
	strncpy(passwords[0], getDefaultPassword(), 254);
	strncpy(passwords[1], getDefaultPassword(), 254);

	if (argc < 1)
		return 0;
	
	if (!strcmp(argv[1], *(passwords + 1)))
	{
		userID = 2;
		printf("Logged in\nWelcome Mark!\n");
	}
	else if (!strcmp(argv[1], *(passwords)))
	{
		userID = 1;
		printf("Logged in\nWelcome Mel!\n");
	}

	return 0;
}
