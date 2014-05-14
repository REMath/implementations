
void foo(int *buf, int len)
{
  for (int i = 0; i < len; i++)
    buf[i] = 0;
  int x = buf[len];
  buf[len] = x + 1;
}

void main()
{
  int buf[100];
  foo(buf, 100);
  int x = buf[100];
}
