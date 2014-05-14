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


#define DEBUG 1

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>


#ifdef DEBUG
	static bool debug = true;
#else
	static bool debug = false;
#endif

// Debug entry points here
void promote_root() {
	if (debug) {
		// set root rights
		printf ("# You are root now...\n");
	}
}

int main(int argc, char *argv[])
{
	if (argc > 1)
	{
		const unsigned nbArgs = argc;
		for (unsigned i=1;i<nbArgs;++i)
		{
#ifdef DEBUG
			if (!strncmp(argv[i],"-debug",6))
			{
				debug = true;
				printf("Move to debugging mode\n");
				// for debugging code and process, let's say you need root rights
				if (strlen(argv[i]) >= 11 && !strncmp(argv[i]+6,":root",5))
				{
					promote_root();
				}
			}
#endif
		}	
	}
	else
	{
		printf("No args...\n");
	}

}



