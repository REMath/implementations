#include "wu-ftpd.h"

uid_t geteuid(void)
{
  return taint();
}

int seteuid(uid_t euid)
{
  if (nondet_int() == 0)
    return 0;
  return -1;
}

int     enable_signaling()
{
  return (0);
}

int     delay_signaling()
{
  return (0);
}

/* Returns the number of bytes written to buf, or -1 if there's an
   error. This'll do it, assuming buf is initially uninitialized. */
int readlink(const char *path, char *buf, int bufsiz)
{
  int n = nondet_int ();
  if (n < bufsiz && n >= 0) {
    buf[n-1] = path[n-1];
    return n;
  }
  return -1;
}

/* Just make sure buf is null-terminated unless we simulate an error. */
char *getcwd(char *buf, size_t size)
{
  if (nondet_int() == 0) {
    return NULL;
  }
  buf [size-1] = taint();
  return buf;
}

