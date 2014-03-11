/*
 * example programm that segfault's a lot.
 * $ gcc -Wall -o segfault segfault.c
 * $ LD_PRELOAD=./assfault.so ./segfault
 */
#include <stdio.h>
#include <signal.h>
void
signal_handler(int sig, siginfo_t *si, void *unused)
{
	fprintf(stderr, "This is the signal handler of the user\n");
}

struct sigaction sa;

int
main()
{
    char *ptr=NULL;
	//sa.sa_flags = SA_SIGINFO;
	//sigemptyset(&sa.sa_mask);
	//sa.sa_sigaction = signal_handler;
    /* redirect action for these signals to our functions */
	//sigaction(SIGSEGV, &sa, NULL);
	//sigaction(SIGILL, &sa, NULL);
	//sigaction(SIGBUS, &sa, NULL);




    fprintf(stderr, "|0| everything looks fine. lets produce a SIGSEGV\n");
	*ptr=1;
	fprintf(stderr, "|1| after first provocated SIGSEGV\n");
    *ptr=1;
    fprintf(stderr, "|2| after second provocated SIGSEGV\n");
    fprintf(stderr, "|X| We survived - enough played today.\n");

    return 0;
}
/*** EOF segfault.c ***/
