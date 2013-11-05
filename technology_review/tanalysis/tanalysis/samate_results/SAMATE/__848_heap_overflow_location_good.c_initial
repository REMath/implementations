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
#include <string.h>
#include <stdio.h>
#include <time.h>
// Binary Russian Dice

char *rand_text() {
	srand(time(NULL));
	unsigned length = (rand() % 25) - 1;
	char *t = malloc(length * sizeof(char));
	if (!t) 
		return NULL;
	unsigned i=0;
	for (;i<length;++i)
	{
		t[i] = (char)((rand() % 26)  + 'a');
	}
	t[i+1] = '\0';
	return t;
}

int main(int argc, char *argv[])
{
	char *buf = (char *)NULL;
	buf = malloc(25*sizeof(char));
	
	if (buf != (char *)NULL)
	{
		char *t = rand_text();
		if (t) {
			strcpy(buf,t);	
			free(t);
		}
		free(buf);
	}
	return 0;
}
