/*  This file is part of Fuzzgrind.
 *  Copyright (C) 2009 Gabriel Campana
 *
 *  This work is licensed under the terms of the GNU GPL, version 3.
 *  See the LICENSE file in the top-level directory.
 */


#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <signal.h>
#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>


#define ERROR(x)     do { perror(x); exit(-1); } while (0)
#define PTRACE(request, pid, addr, data) do {     \
    if (ptrace(request, pid, addr, data) == -1) { \
        ERROR("ptrace");                          \
    }                                             \
} while (0)


int bad_signal(int sig) {
    int ret = (sig == SIGSEGV || sig == SIGILL || sig == SIGABRT);
    
    if (ret) {
        printf("[+] oops, we received %s\n", strsignal(sig));
    }
    
    return ret;
}


int main(int argc, char *argv[]) {
   /*siginfo_t si;*/
    int status;
    pid_t pid;
    
    if (argc < 2) {
        printf("Usage: %s <program> [args]\n", argv[0]);
        exit(0);
    }
    
    switch (pid = fork()) {
        case 0:
            PTRACE(PTRACE_TRACEME, 0, NULL, NULL);
            execvp(argv[1], &argv[1]);
            ERROR("exec()");
            break;
            
        case -1:
            ERROR("fork()");
            break;
            
        default:
            break;
    }
    
    while (1) {
        if (waitpid(pid, &status, 0) == -1) {
            ERROR("waitpid");
        }
        
        /* the child process was stopped by delivery of a signal */
        if (WIFSTOPPED(status)) {
            /*memset(&si, 0, sizeof(si));
            PTRACE(PTRACE_GETSIGINFO, pid, 0, &si);
            
            printf("[+] 0x%08x: %s\n", (unsigned int)si.si_addr, strsignal(si.si_signo));*/
            /*printf("[+] signal(%s)\n", strsignal(WSTOPSIG(status)));*/
            if (bad_signal(WTERMSIG(status))) {
                return WSTOPSIG(status);
            }
            
            PTRACE(PTRACE_CONT, pid, NULL, 
                   WSTOPSIG(status) == SIGTRAP ? 0 : WSTOPSIG(status));
        }
        
        /* the child terminated normally */
        else if (WIFEXITED(status)) {
            /* printf("[+] exit(%d)\n", WEXITSTATUS(status)); */
            return 0;
        }
        
        /* the child process was terminated by a signal */
        else if (WIFSIGNALED(status)) {
            /* printf("[+] signaled(%s)\n", strsignal(WTERMSIG(status))); */
            return bad_signal(WTERMSIG(status)) ? WTERMSIG(status) : 0;
        }
        
        /* the child process was resumed by delivery of SIGCONT */
        else if (WIFCONTINUED(status)) {
            /* printf("[+] sigcont\n"); */
        }
    }
    
    return 0;
}
