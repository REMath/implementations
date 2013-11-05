
#include <stdlib.h>
#include <stdio.h>

int g = 0;

int main()
{
  int &x;
  x = g;
  x = 1;

  // printf("g = %d\n", g);
  return 0;
}

