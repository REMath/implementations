// mypopen.c            see license.txt for copyright and terms of use
// code for myopen.h
// this module's implementation is in C, and not dependent on anything
// else in smbase, so it can be extracted and used independently

#include "mypopen.h"    // this module

#include <stdlib.h>     // exit, perror
#include <stdio.h>      // printf
#include <unistd.h>     // pipe, read, etc.
#include <string.h>     // strlen
#include <sys/types.h>  // pid_t
#include <sys/wait.h>   // wait

#define STDIN 0
#define STDOUT 1
#define STDERR 2

#ifndef max
  #define max(a,b) ((a)>(b)?(a):(b))
#endif

// -------------------- helpers ----------------------
static void die(char const *fn)
{
  perror(fn);
  exit(2);
}


void makePipe(int *readEnd, int *writeEnd)
{
  int pipes[2];
  if (pipe(pipes) < 0) {
    die("pipe");
  }

  *readEnd = pipes[0];
  *writeEnd = pipes[1];
}


// ------------------- execvp -------------------
struct ExecvArgs {
  char const *file;
  char const * const *argv;
};

static void call_execvp(void *_args)
{
  char *msg;
  struct ExecvArgs *args = (struct ExecvArgs*)_args;

  // I think execvp is declared incorrectly; I cast to circumvent
  execvp(args->file, (char * const *)(args->argv));

  // execvp only returns if there was an error; if this happens,
  // the error message will be printed to the stderr pipe if
  // it was redirected
  msg = (char*)malloc(strlen(args->file) + 6 + 2 + 1);
  sprintf(msg, "execvp: %s", args->file);
  die(msg);
}

int popen_execvp(int *parentWritesChild, int *parentReadsChild,
                 int *childStderr,
                 char const *file, char const * const *argv)
{
  struct ExecvArgs args;
  args.file = file;
  args.argv = argv;

  return popen_pipes(parentWritesChild, parentReadsChild, childStderr,
                     call_execvp, &args);
}


// ------------------ primary function ------------------
int popen_pipes(int *parentWritesChild, int *parentReadsChild,
                int *readChildStderr,
                execFunction func, void *extraArgs)
{
  int childReadsParent;
  int childWritesParent;
  int childWritesStderr;
  int childPid;
  int stderrToStdout = 0;

  // create pipes
  makePipe(&childReadsParent, parentWritesChild);
  makePipe(parentReadsChild, &childWritesParent);
  if (parentReadsChild == readChildStderr) {
    // caller wants child stdout and stderr going to same place
    stderrToStdout = 1;
    *readChildStderr = *parentReadsChild;
    readChildStderr = NULL;     // most of the code behaves as if stderr isn't being changed
  }
  else if (readChildStderr) {
    makePipe(readChildStderr, &childWritesStderr);
  }

  // fork a child
  childPid = fork();
  if (childPid < 0) {
    die("fork");
  }

  if (childPid != 0) {      // parent
    // close the pipe ends I'm not going to use
    if (close(childReadsParent) < -1   ||
        close(childWritesParent) < -1  ||
        (readChildStderr && close(childWritesStderr) < -1)) {
      die("close");
    }

    return childPid;
  }

  else {                    // child
    // rearrange file descriptors so stdin and stdout of the
    // program we're about to exec will talk to parent

    // sleep so debugger can attach
    //sleep(10);

    // close the pipe ends I'm not going to use
    if (close(*parentReadsChild) < -1   ||
        close(*parentWritesChild) < -1  ||
        (readChildStderr && close(*readChildStderr) < -1)) {
      die("close");
    }

    // first, close parent's stdin/stdout
    if (close(STDIN) < -1   ||
        close(STDOUT) < -1  ||
        (readChildStderr && close(STDERR) < -1)) {
      die("close");
    }

    // now, duplicate the pipe fds to stdin/stdout
    if (dup2(childReadsParent, STDIN) < -1                         ||
        dup2(childWritesParent, STDOUT)	< -1                       ||
        (readChildStderr && dup2(childWritesStderr, STDERR) < -1)  ||
        (stderrToStdout && dup2(childWritesParent, STDERR) < -1)   ) {
      die("dup2");
    }

    // finally, close the original pipe fds
    if (close(childReadsParent) < -1   ||
        close(childWritesParent) < -1  ||
        (readChildStderr && close(childWritesStderr) < -1)) {
      die("close");
    }

    // ok, fds are in order.  let's exec the child program
    func(extraArgs);

    // not reached; silence warning
    return -1;
  }
}


// ------------------ test code ----------------------
#ifdef TEST_MYPOPEN

int main()
{
  char buf[80];
  int stat;

  // try cat
  {
    int in, out;
    char const *argv[] = { "cat", NULL };
    int pid = popen_execvp(&in, &out, NULL, argv[0], argv);
    printf("child pid is %d\n", pid);

    if (write(in, "foo\n", 4) != 4) {
      die("write");
    }
    if (read(out, buf, 4) != 4) {
      die("read");
    }

    if (0==memcmp(buf, "foo\n", 4)) {
      printf("cat worked for foo\n");
    }
    else {
      printf("cat FAILED\n");
      return 2;
    }

    if (write(in, "bar\n", 4) != 4) {
      die("write");
    }
    if (read(out, buf, 4) != 4) {
      die("read");
    }

    if (0==memcmp(buf, "bar\n", 4)) {
      printf("cat worked for bar\n");
    }
    else {
      printf("cat FAILED\n");
      return 2;
    }

    close(in);
    close(out);

    printf("waiting for cat to exit..\n");
    if (wait(&stat) < 1) {
      perror("wait");
    }
    else {
      printf("cat exited with status %d\n", stat);
    }
  }

  // try something which fails
  {
    int in, out, err;
    int len;
    char const *argv[] = { "does_not_exist", NULL };
    int pid = popen_execvp(&in, &out, &err, argv[0], argv);
    printf("child pid is %d\n", pid);

    printf("waiting for error message...\n");
    len = read(err, buf, 78);
    if (len < 0) {
      die("read");
    }
    if (buf[len-1] != '\n') {
      buf[len++] = '\n';
    }
    buf[len] = 0;
    printf("error string: %s", buf);   // should include newline from perror

    close(in);
    close(out);
    close(err);

    printf("waiting for child to exit..\n");
    if (wait(&stat) < 1) {
      perror("wait");
    }
    else {
      printf("child exited with status %d\n", stat);
    }
  }

  // also fails, but with stdout and stderr going to same pipe
  {
    int in, out;
    int len;
    char const *argv[] = { "does_not_exist", NULL };
    int pid = popen_execvp(&in, &out, &out, argv[0], argv);
    printf("out==err: child pid is %d\n", pid);

    printf("waiting for error message...\n");
    len = read(out, buf, 78);
    if (len < 0) {
      die("read");
    }
    if (buf[len-1] != '\n') {
      buf[len++] = '\n';
    }
    buf[len] = 0;
    printf("error string: %s", buf);   // should include newline from perror

    close(in);
    close(out);

    printf("waiting for child to exit..\n");
    if (wait(&stat) < 1) {
      perror("wait");
    }
    else {
      printf("child exited with status %d\n", stat);
    }
  }
  
  printf("mypopen worked!\n");
  return 0;
}

#endif // TEST_POPEN
