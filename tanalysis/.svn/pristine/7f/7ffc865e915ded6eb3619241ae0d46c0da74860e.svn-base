#include "../wu-ftpd.h"

/* resolved is an *input*, initially uninitialized */
char *fb_realpath(const char *path, char *resolved)
{
  int rootd;
  char wbuf[MAXPATHLEN];
  int resultcode;
  char tmp [MAXPATHLEN];
  int p, q;

  (void) strncpy(resolved, path, MAXPATHLEN - 1);
  resolved[MAXPATHLEN - 1] = EOS;

 loop:
  /* Once this loop terminates, the final slash in resolved has been 
   * replaced with an EOS, and p points to the filename after it.
   */
  q = istrrchr(resolved, '/');
  if (q != -1) {
    /* p is whatever's after the last slash */
    p = q + 1;               

    if (q == 0) {
      /* Don't do anything. Originally, q was a pointer, we set it 
       * to "/", and chdir'd to "/". Since we're chopping out the chdir, 
       * we don't need to do anything.
       */
    } else {
      /* chops off the last slash and terminates resolved[] at it */
      do {
        --q;
      } while (q > 0 && resolved[q] == '/');
      resolved[q+1] = EOS;            
      q = 0;          
    }

  }
  else
    /* no slashes found ==> just a filename */
    p = 0;

  if (resolved[p] != EOS) {
    resultcode = nondet_int();
    /* If lstat() didn't fail.... */
    if (resultcode == 0) {
      int symlinks =  0;
      int n;

      /* If this was a symlink.... */
      if (nondet_int()) {
        if (++symlinks > 512) {
          return NULL;
        }
        strcpy(tmp, resolved + p);
        n = readlink(tmp, resolved, MAXPATHLEN);
        if (n < 0) {
          return NULL;
        }
        resolved[n] = EOS;

        goto loop;
      }
      /* p was originally a pointer, and it could have been set to "" 
       * here if the final component were a directory.
       *
       * That's hard to do with an integer, so I'm slicing that
       * out. This example's already plenty complex.
       */
    }
  }

  /* wbuf contains the filename, but not the path to it */
  strcpy(wbuf, resolved + p);

  if (getcwd(resolved, MAXPATHLEN) == NULL)
    return NULL;

  if (resolved[0] == '/' && resolved[1] == EOS)
    rootd = 1;
  else
    rootd = 0;
 
  if (wbuf[0] != EOS) {
    if (strlen(resolved) + strlen(wbuf) + rootd + 1 > MAXPATHLEN) {
      return NULL;                                
    }
    if (rootd == 0)
      (void) strcat(resolved, "/");

    /* BAD */                            
    (void) r_strcat(resolved, wbuf);
  }
  return (NULL);
}

int main ()
{
  char pathname [MAXPATHLEN];
  char resolved [MAXPATHLEN];

  pathname [MAXPATHLEN-1] = EOS;
  resolved [MAXPATHLEN-1] = EOS;

  fb_realpath(pathname, resolved);

  return 0;
}
