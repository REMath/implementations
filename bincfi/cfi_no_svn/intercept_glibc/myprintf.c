#define _GNU_SOURCE
#include <dlfcn.h>
//#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <dlfcn.h>
static void *libc_handle = NULL;
static void *handler = NULL;

void
printf(){
	
	libc_handle = dlopen("libc.so", RTLD_NOW);

	handler = dlsym( libc_handle, "printf");

}
void
puts(){
	
	libc_handle = dlopen("libc.so", RTLD_NOW);

	handler = dlsym( libc_handle, "printf");

}

void main(){
	//printf("this is interception library\n");
}
