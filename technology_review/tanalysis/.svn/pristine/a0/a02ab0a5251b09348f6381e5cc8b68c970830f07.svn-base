#include "parse_dns_reply.h"
#include "../stubs.h"

#define DATA 100

int main (void)
{
  unsigned char *p;
  int size;
  char *rr_txt;

  /* Added for STAC: consider the data as input dependent! */
  p = taint();

  size = nondet_int ();
  rr_txt = (char *) malloc (size + 1);
  if (rr_txt == 0)
    return 0;

  /* BAD */
  strncpy (rr_txt, (char *) p + 1, *p);
  /* BAD */
  rr_txt[*p] = 0;
  return 0;
}
