#include "../constants.h"

extern int nondet_int();

void ftpls (char *line)
{
    int j;

    /* Stop at either:
     *  (1) first char before EOS which isn't in "-rwxdls", or,
     *  (2) first EOS
     */
    for(j = 0; line[j] != EOS; ++j)
      if (!strchr("-", line[j]))
        break;

    if(j == J && line[j] == ' ') {	/* long list */
      /* BUG! No bounds check. */
      char user[USERSZ];
      /* BAD */
      r_strcpy (user, line + j);
    }
}

int main ()
{
  char out [INSZ];
  int out_l;
  int dirmode;
  static const char npf[] = NPF;
  const int npfsize = NPFSZ;
  int c;

  dirmode = 0;

  out_l = 0;
  out[INSZ-1] = EOS;

 top:

  while((c = taint()) != EOF) {
    if(c == '\r')
      c = '\n';
    if(c == '\n') {
      if(dirmode) {
        ftpls(out);
      } else {
        if(!out_l)
          continue;
        if (out_l > npfsize) {
          dirmode = 1;
          goto top;
        }
      }
      out_l = 0;
    } else {
      out[out_l] = c;
      out_l++;
      if (out_l > INSZ-1)
        return ERR;
    }
  }

  return 0;
}
