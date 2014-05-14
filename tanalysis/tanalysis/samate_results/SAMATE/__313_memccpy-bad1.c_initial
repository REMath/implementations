/*
  PLOVER: BUFF.OVER
*/

/*
	No bounds checking, null character
*/

#include <stdio.h>
#include <string.h>

#define MAXSIZE 40

void test(char *str){
	char buf[MAXSIZE];
	memccpy(buf, str, 0, strlen(str));
	printf("results: %s\n", buf);
}

int main(int argc, char **argv){
	char *userstr;
	if(argc > 1){
		userstr = argv[1];
		test(userstr);
	}
	return 0;
}
