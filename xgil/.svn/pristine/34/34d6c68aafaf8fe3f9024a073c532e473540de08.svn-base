
void decrement_access(int *buf, int n)
{
  int *p = buf;
  while (n) {
    *p++ = 0;
    n--;
  }
}

void increment_access(int *buf, int n)
{
  for (int i = 0; i != n; i++)
    *buf++ = 0;
}

void increment_pointer(int *buf, int *end)
{
  while (buf != end)
    *buf++ = 0;
}

void main()
{
  int buf[100];
  decrement_access(buf, 100);
  increment_access(buf, 100);
  increment_pointer(buf, &buf[100]);
}
