#include "../constants.h"

void message_write (char *msg, int len)
{
  int i;
  int j;
  char buffer[BUFSZ];

  int limit = BUFSZ - 1;

  for (i = 0; i < len; ) {
    for (j = 0; i < len && j < limit; ){
      if (i + 1 < len 
          && msg[i] == '\n' 
          && msg[i+1]== '.') {
        buffer[j] = msg[i]; /* Suppose j == limit - 1 */
        j++;
        i++;
        buffer[j] = msg[i]; /* Now j == limit */
        j++;
        i++;
        /* BAD */
        buffer[j] = '.';    /* Now j == limit + 1 = sizeof(buffer) */
        j++;
      } else {
        buffer[j] = msg[i];
        j++;
        i++;
      }
    }
  }
}

int main ()
{
  char msg [INSZ];

  /* Added for STAC: the input data must be considered tainted! */
  msg[0] = taint();

  message_write (msg, INSZ);
  
  return 0;
}

