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

  for (_i = 0; _i < n; _i++) {
    dest[_i] = src[_i]; // DO NOT CHANGE THE POSITION OF THIS LINE
    if (src[_i] == EOS)
      break;
  }
  return dest;
}

int istrstr(const char *haystack, const char *needle)
{
  int len;
  int i;
  int j;

  len = 0;
  while (needle[len] != EOS) len++;

  for (i = 0; haystack[i] != EOS; i++) {
    for (j = 0; j < len-1; j++) {
      if (haystack[i+j] == EOS) break;
      if (haystack[i+j] != needle[j]) break;
    }
    if (j == len-1 &&
        haystack[i+len-1] == needle[len-1])
      return i;
  }

  return NULL;
}

