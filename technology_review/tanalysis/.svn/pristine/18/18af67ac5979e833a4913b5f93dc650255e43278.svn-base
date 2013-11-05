#include "../wu-ftpd.h"

char *
realpath(const char *pathname, char *result, char* chroot_path)
{
  char curpath[MAXPATHLEN],
    workpath[MAXPATHLEN],
    linkpath[MAXPATHLEN],
    namebuf[MAXPATHLEN],
    *where;
  int len;

  where = curpath;

  /* Stand-in for checking stat fields. */
  if (nondet_int() == 1) {
    len = readlink(namebuf, linkpath, MAXPATHLEN);
    if (len <= 0)
      return NULL;
  
    linkpath[len] = EOS;

    if (linkpath[0] == '/')
      workpath[0] = EOS;
    if (where[0] != EOS) {
      /* BAD */
      r_strcat(linkpath, "/");
      /* BAD */
      r_strcat(linkpath, where);
    }
    /* BAD */
    r_strcpy(curpath, linkpath);
  }

  return result;
}

int main ()
{
  char pathname [MAXPATHLEN];
  char result [MAXPATHLEN];
  char chroot_path [MAXPATHLEN];

  /* Don't use too big a pathname; we're not trying to overflow curpath */
  pathname [MAXPATHLEN-1] = EOS;
  result [MAXPATHLEN-1] = EOS;
  chroot_path [MAXPATHLEN-1] = EOS;

  realpath(pathname, result, chroot_path);

  return 0;
}
