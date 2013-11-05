#include "../constants.h"

int parse_expression (char *str) {
  char *except;
  char str2 [LINE_LENGTH];
  
  except = strchr (str, 'e');
  if (except) {
    // SAFE: the 'e' is not copied
    strncpy (str2, str, (unsigned int)(except-str));
  } else {
    // UNSAFE: can copy up to LINE_LENGTH+1 characters
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
