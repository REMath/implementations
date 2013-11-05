
void bar(int y[])
{
  y[0] = 0;
}

void foo(int x)
{
  int buf[x + 2 + 2];
  int wbuf[x - 2 - 2];
  int *pbuf[x * 2];
  int (*abuf2[x * 4])();
  buf[x - 1] = 0;
  bar(buf);
}

void borken(int x)
{
  // this manages to break the current implementation. TODO: fix
  // int (*abuf)()[x];
}

int trysize(int x)
{
  return sizeof(int[x]);
}
