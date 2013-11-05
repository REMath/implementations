#include <stdio.h>

#include "work.h"

int main()
{
  printf("Running...\n");

  int *buf;
  int count, ind;

  GetWork(&buf, &count);
  for (ind = 0;;) {
    DoWork(buf, count, ind);
    ind++;
  }

  return 0;
}

