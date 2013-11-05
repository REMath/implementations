
void* malloc(int);

void bar(int *buf, int size)
{
  for (int i = 0; i < size; i++)
    buf[i] = 0;
}


void foo(int len)
{
  int *xbuf = malloc(len * sizeof(int));
  bar(xbuf, len);
}

