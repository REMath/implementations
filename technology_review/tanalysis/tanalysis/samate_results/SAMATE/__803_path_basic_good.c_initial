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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int printFile(const char *fileName)
{
	FILE *fp = (FILE *)NULL;
	if ((fp = fopen(fileName, "r")))
	{
		char buffer[512];
		unsigned int lNumber = 0;
		while (fgets(buffer, 512, fp))
		{
			printf("%3d: %s", ++lNumber, buffer);
		}		
		fclose(fp);
		return 0;
	}
	return 1;
}

/* 
	One of the most basic filtering, remove the '/'
*/
void inputFiltering(char *fName)
{
	char buf[256]="";
	char *c = fName, *b = buf;
	for (;*c != '\0';c++)
	{
		while (*c == '/') c++;
		*b++ = *c;
	}
	strncpy(fName, buf, 255);
}


int main(int argc, char *argv[])
{
	// Open the file in the command line
	if (argc > 1)
	{
		char fName[256] = "";
		strncpy(fName, argv[1], 255);
		inputFiltering(fName);

		if (printFile(fName))
		{
			printf("Argument error, the file is not readable.\n");
		}
	}
	return 0;	
}
