#include <stdio.h>
#include <unistd.h>

void main(){
	int uid = getuid();
	int i;
	for(i=0;i<20000000;i++){
		getuid();
	}
}
