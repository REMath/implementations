
#include <stdio.h>
#include "work.h"

static int total = 10;

void GetWork(int **buf, int *count)
{
  *buf = (int*) malloc(total * sizeof(int));
  *count = total;
}

void DoWork(int *buf, int count, int ind)
{
  printf("%d\n", ind);
  buf[ind] = 0;
}
