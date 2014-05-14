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

#include <string.h>
#include <stdlib.h>
#include <stdio.h>



const char *whitelist[5] = {
	"users_site.dat",
	"users_reg.dat",
	"users_info.dat",
	"admin.dat",
	"services.dat.cxx"
};


int allowed(const char *_str) {
	for (unsigned i = 0; i < 5; i++)
	{
		if (!strcmp(whitelist[i], _str))
			return 0;
	}
	return 1;
}


void printLine(const char *fileName)
{
	FILE *fp = (FILE *)NULL;
	if ((fp = fopen(fileName, "r")))
	{
		char buff[512];
		if (fgets(buff, 512, fp))
		{
			printf ("%s\n", buff);
		}
		fclose(fp);
	}
}


int main(int argc, char *argv[])
{
	if (argc > 1)
	{
		char fName[1][256];
		strncpy(fName[0],argv[1],255);
		if (allowed(fName[0]))
			printLine(fName[0]);	
	}
	
	
	return 0;
}
