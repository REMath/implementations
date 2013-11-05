#include "../stubs.h"

#define ADDRSIZE        500 // originally 500
#define PSBUFSIZE       512
#define MAXNAME		(4 * 512 / 5)
#define NOCHAR		-1
#define TRUE 1
#define FALSE 0

int main (void)
{
  // originally function arguments
  char addr[ADDRSIZE];
  char pvpbuf[PSBUFSIZE];

  int p, q, q_old;
  int c;

  int pvpbuf_end = sizeof (pvpbuf);

  int bslashmode;
  int i;

  /* Added for STAC: the input data must be considered tainted! */
  addr[0] = taint();
  
  p = 0;
  q = 0;
  bslashmode = FALSE;

  c = NOCHAR;

  q_old = q;
  do
  {
    // bounds check and write lookahead (c) to pvpbuf
    if (c != NOCHAR && !bslashmode)
    {
      if (q >= pvpbuf_end - 1)
	return 0;
      pvpbuf[q] = c;
      q++;
    }

    // read next input char
    c = addr[p];
    p++;
    if (c == EOS)
      break;

    //assert (q < pvpbuf_end);
    /*BAD*/  
    pvpbuf[q] = EOS; // precautiously write EOS to dest

    if (bslashmode)
    {
      bslashmode = FALSE;

      //assert (q < pvpbuf_end);
      /*BAD*/	
      pvpbuf[q] = '\\';
      q++;
      continue;
    }

    if (c == '\\')
      bslashmode = TRUE;
    if (c == NOCHAR) // not supposed to be in the input alphabet
      continue; // skip bounds check on next for loop so another \ can be copied
    if (c == EOS)
      break;
  } while (1);

  if (q_old != q)
  {
    //assert (q < pvpbuf_end);
    /*BAD*/
    pvpbuf[q] = 0;
    q++;

    if (q - q_old > MAXNAME)
      return 0;
  }

  return 0;
}
