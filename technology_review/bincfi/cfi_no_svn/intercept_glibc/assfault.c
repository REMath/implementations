/*
 * someone@segfault.net
 *
 * This is published non-proprietary source code of someone without a
 * name...someone who dont need to be named....
 *
 * You do not want to use this on productivity systems - really not.
 *
 * This preload-library recovers from a SIGSEGV - for fun purposes only!
 *
 * $ gcc -Wall -O2 -fPIC -DDEBUG -c assfault.c
 * $ ld -Bshareable -o assfault.so assfault.o -ldl -lopdis
 # $ LD_PRELOAD=./assfault.so netscape &
 */
#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <dlfcn.h>
#include <ucontext.h>
#include <opdis/opdis.h> //the disassambler opdis

#define REPLACE(a, x, y) if ( !(o_##x = dlsym(##a , ##y)) )\
            { fprintf(stderr, ##y"() not found in libc!\n");\
                exit(-1); }
#ifdef DEBUG
# define DEBUGF(a...)    do{fprintf(stderr, "%s[%d]", __FILE__, __LINE__); \
                           fprintf(stderr, ##a);}while(0)
#else
# define DEBUGF(a...)
#endif

#define err_exit(str) do{fprintf(stderr, "ERROR:%s\n", str);exit(-1);}while(0);

static void *(*o_signal)(int, struct sigaction *sa, struct sigaction *old);
static void *libc_handle = NULL;
//static int sigcount;
static struct sigaction sa;

static opdis_insn_t insn;
void
assfault_handler(int sig, siginfo_t *si, void *unused)
{
    int i = 0;
    opdis_t o;
    void * location;

    fprintf(stderr,"Got SIGSEGV at address: 0x%lx\n",(long) si->si_addr);
    struct ucontext *u = (struct ucontext *)unused;
    fprintf(stderr,"before change, EIP:%lx\n",(long)u->uc_mcontext.gregs [REG_EIP]);
    location = u->uc_mcontext.gregs [REG_EIP];
    //disassemble_mem(location, 32);    

    opdis_buf_t buf = opdis_buf_alloc( 33, location );
    if(!(i=opdis_buf_fill( buf, 0, location, 32 )))
		printf("buffer fill failed\n");	
    //fprintf(stderr,"write %d bytes into buffer\n",i);
    //fprintf(stderr,"buffer len:%d\n",buf->len);
    //fprintf(stderr,"buffer vma:%lx\n",(long)buf->vma);

    o = opdis_init();
    //i = opdis_disasm_insn_size(o, buf, location);
    memset(&insn,0,sizeof(insn));
    fprintf(stderr, "the fault insn is ===>  ");
    opdis_disasm_insn(o, buf, location, &insn);
    //opdis_disasm_linear(o,buf,location,32);
    i = insn.size;
    if(i>0)
	u->uc_mcontext.gregs [REG_EIP] += i;
    else
	u->uc_mcontext.gregs [REG_EIP] += 1;
    fprintf(stderr,"after  change, EIP:%lx\n",(long)u->uc_mcontext.gregs [REG_EIP]);
    opdis_term(o);
 }

static void
assfault_init(void)
{
    if ( (libc_handle = dlopen("libc.so", RTLD_NOW)) == NULL)
        if ( (libc_handle = dlopen("libc.so.6", RTLD_NOW)) == NULL)
            err_exit("error loading libc!");

    /* get the address of the original signal() -function in libc */
    if ( !(o_signal = dlsym( libc_handle , "sigaction")) ) { fprintf(stderr, "sigaction""() not found in libc!\n"); exit(-1); };
	sa.sa_flags = SA_SIGINFO;
	sigemptyset(&sa.sa_mask);
	sa.sa_sigaction = assfault_handler;
    /* redirect action for these signals to our functions */
	o_signal(SIGSEGV, &sa, NULL);
	o_signal(SIGILL, &sa, NULL);
	o_signal(SIGBUS, &sa, NULL);

	dlclose(libc_handle);
}

/*
 * called by dynamic loader.
 */
void
_init(void)
{
    if (libc_handle != NULL)
        return; /* should never happen */

    assfault_init();
    DEBUGF("assfault.so activated.\n");
}   
/*** EOF assfault.c ***/

