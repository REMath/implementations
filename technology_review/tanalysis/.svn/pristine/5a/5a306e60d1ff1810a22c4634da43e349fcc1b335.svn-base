#define BUF 512
#define GECOS 2
#define LOGIN (512 + 2)/GECOS

#include "../stubs.h"

int
main (void)
{
  // these were parameters
  char login[LOGIN + 1];
  char gecos[GECOS + 1];

  char buf[BUF + 1];
  char c;
  int i, j;
  
  /* Added for STAC: the input data must be considered tainted! */
  login[0] = gecos[0] = taint();

  login[(int) (sizeof login - 1)] = EOS;
  gecos[(int) (sizeof gecos - 1)] = EOS;

  i = 0;
  if (gecos[i] == '*')
    i++;

  c = gecos[i];
  j = 0;
  while (c != EOS && c != ',' && c != ';' && c != '%')
  {
    if (c == '&')
    {
      /* BAD */
      (void) strcpy (buf + j, login);
      while (buf[j] != EOS)
	j++;
    }
    else
    {
      /* BAD */
      buf[j] = c;
      j++;
    }	    
    i++;
    c = gecos[i];
  }
  buf[j] = EOS;
  return 0;
}
