#include "../constants.h"

int parse_expression (char *str) {
  int ind;
  char str2 [LINE_LENGTH];

  ind = nondet_int ();
  if (ind < -1 || ind >= LINE_LENGTH)
    return -1;

  if (ind != -1) {
    strncpy (str2, str, ind);
  } else {
    /* BAD */
    r_strcpy (str2, str);
  }

  return 0;
}

int main ()
{
  char A [LINE_LENGTH+1];
  
  /* Added for STAC: the input data must be considered tainted! */
  A[0] = taint();
  
  A[LINE_LENGTH] = EOS;

  parse_expression (A);
  return 0;
}
