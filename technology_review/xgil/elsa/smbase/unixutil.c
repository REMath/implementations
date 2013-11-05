// unixutil.c            see license.txt for copyright and terms of use
// code for unixutil.h

#include "unixutil.h"   // this module

#include <unistd.h>     // write
#include <assert.h>     // assert
#include <sys/time.h>   // struct timeval
#include <sys/types.h>  // select
#include <unistd.h>     // select
#include <stdio.h>      // perror

// 12/13/04: according to rfistman at hotmail, this is required to get
// FD_ZERO to work on OS X; or should I just #include sys/select.h?
// how portable is that?
//
// A little googling reveals this page documenting sys/select.h:
//
//   http://www.opengroup.org/onlinepubs/009695399/basedefs/sys/select.h.html
//
// It says it was introduced to POSIX in 2000, which I interpret to mean
// older systems are likely to not have it.  Indeed, I see messages from
// people reporting that this file is missing, e.g.,
//
//   http://curl.haxx.se/mail/archive-2003-05/0161.html
//   http://archives.postgresql.org/pgsql-hackers/1997-01/msg00878.php
//
// So I will just stick with string.h until I see a problem with it.
#include <string.h>     // bzero via FD_ZERO on OS X

#ifdef __MINGW32__
  // on mingw32, fd_set lives in winsock.h
  #include <winsock.h>
#endif


int writeAll(int fd, void const *buf, int len)
{
  int written = 0;
  while (written < len) {
    int result = write(fd, ((char const*)buf)+written, len-written);
    if (result < 0) {
      return 0;    // failure
    }
    written += result;
  }
  assert(written == len);
  return 1;        // success
}


int readString(int fd, char *str, int len)
{ 
  int count = read(fd, str, len-1);
  if (count < 0) {
    return 0;      // failure
  }
  str[count]=0;

  // remove trailing newlines (or NULs), if any
  while (count>0 && (str[count-1] == '\n' || str[count-1] == 0)) {
    count--;
    str[count] = 0;
  }

  return 1;
}


int canRead(int fd)
{
  fd_set set;
  struct timeval tv;
  int res;

  // check only 'fd'
  FD_ZERO(&set);
  FD_SET(fd, &set);

  // do not block at all
  tv.tv_sec = 0;
  tv.tv_usec = 0;

  res = select(fd+1, &set, NULL, NULL, &tv);
  if (res == -1) {
    perror("select");     // not ideal...
    return 0;
  }
  
  return res;             // 0 or 1
}


// EOF
