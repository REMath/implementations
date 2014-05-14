// mypopen.h            see license.txt for copyright and terms of use
// open a process and yield pipes to its stdin/stdout/stderr

#ifndef MYPOPEN_H
#define MYPOPEN_H

#ifdef __cplusplus
extern "C" {
#endif

// create a pipe and retrieve the read and write file descriptors
void makePipe(int *readEnd, int *writeEnd);

// function to exec something, given some args to say how; it must
// *not* return
typedef void (*execFunction)(void *extraArgs);

// generic popen with generic exec function; the first two int* must
// not be NULL, but the third can be NULL (in which case stderr will
// not be redirected); alternatively, if 'childStderr' ==
// 'parentReadsChild', then the child's stderr will be directed to the
// same pipe as its stdout
int popen_pipes(int *parentWritesChild, int *parentReadsChild,
                int *childStderr,
                execFunction func, void *extraArgs);

// version that calls execvp internally
int popen_execvp(int *parentWritesChild, int *parentReadsChild,
                 int *childStderr,
                 char const *file, char const * const *argv);


#ifdef __cplusplus
}
#endif

#endif // MYPOPEN_H
