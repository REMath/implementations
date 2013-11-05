#include "../wu-ftpd.h"

char *
realpath(const char *pathname, char *result, char* chroot_path)
{
  char curpath[MAXPATHLEN],
    workpath[MAXPATHLEN],
    linkpath[MAXPATHLEN],
    namebuf[MAXPATHLEN];
  int len;
  int where;
  int ptr;
  int last;

  if (result == NULL)
    return(NULL);

  if(pathname == NULL){
    *result = EOS; 
    return(NULL);
  }

  strcpy(curpath, pathname);

  if (pathname[0] != '/') {
    uid_t userid;
		
    if (!getcwd(workpath,MAXPATHLEN)) {
      userid = geteuid();
      delay_signaling();
      seteuid(0);
      if (!getcwd(workpath,MAXPATHLEN)) {
        strcpy(result, ".");
        seteuid(userid);
        enable_signaling();
        return (NULL);
      }
      seteuid(userid);
      enable_signaling();
    }
  } else
    workpath[0] = EOS;

  where = 0;
  while (curpath[where] != EOS) {
    if (!strcmp(curpath + where, ".")) {
      where++;
      continue;
    }

    strcpy(namebuf, workpath);
    for (last = 0; namebuf[last] != EOS; last++)
      continue;
    if ((last == 0) || (namebuf[--last] != '/'))
      /* BAD */
      r_strcat(namebuf, "/");

    /* BAD */
    r_strcat(namebuf, curpath + where);
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
