#include <stdio.h>
#include <string.h>

#define	MAXSIZE		40

char *shortstr(char *p, int n, int targ)
{
	if(n > targ)
		return shortstr(p+1, n-1, targ);
	return p;
}

void test(char *str)
{
	char buf[MAXSIZE], *str2;

	str2 = shortstr(str, strlen(str), MAXSIZE-1);
	strcpy(buf, str2);
	printf("result: %s\n", buf);
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

