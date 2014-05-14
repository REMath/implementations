#include "../constants.h"

/* Input of death is:
 *   (OTHER)^2(' ')(NOT_EOS)^(sizeof(user))
 *
 */

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
  char in [INSZ];
  
  /* Added for STAC: the input data must be considered tainted! */
  in[0] = taint();
  
  in [INSZ-1] = EOS;

  ftpls(in);

  return 0;
}
