#include "stubs.h"

/****************************************************************************
 *
 * Begin duplicate relevant functions.
 *
 ***************************************************************************/

char *r_strcat(char *dest, const char *src)
{
  int i, j;
  char tmp;
  i = 0; j = 0;
  while (dest[i] != EOS)
    i++;
  do {
    tmp = src[j];
    /* replace this line.... */
    dest[i] = tmp;
    i++; j++;
  } while (src[j] != EOS);

  /* strcat man page says that strcat null-terminates dest */
  /* r_strcat RELEVANT */
  dest[i] = EOS;

  return dest;
}

char *r_strcpy (char *dest, const char *src)
{
  int i;
  char tmp;
  for (i = 0; ; i++) {
    tmp = src[i];
    /* r_strcpy RELEVANT */
    dest[i] = tmp; // DO NOT CHANGE THE POSITION OF THIS LINE
    if (src[i] == EOS)
      break;
  }
  return dest;
}

int istrchr(const char *s, int c)
{
  int i;
  for (i = 0; s[i] != EOS; i++)
    if (s[i] == c)
      return i;

  return (c == EOS) ? i : -1;
}

char *r_strncpy (char *dest, const char *src, int n)
{
  int _i;

  /* r_strncpy RELEVANT */
  dest[n];

  for (_i = 0; _i < n; _i++) {
    dest[_i] = src[_i]; // DO NOT CHANGE THE POSITION OF THIS LINE
    if (src[_i] == EOS)
      break;
  }
  return dest;
}

/* We do the copy backwards in order to trip upper bounds assertion
 * failures more quickly. */
void *r_memcpy(char *dest, const char *src, int n)
{
  int i;

  /* r_memcpy RELEVANT */
  dest[n-1];

  for (i = n-1; i >= 0; i--) {
    dest[i] = src[i];
  }
  return dest;
}

