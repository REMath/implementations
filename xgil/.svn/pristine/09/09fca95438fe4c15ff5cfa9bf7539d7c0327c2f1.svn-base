
void bad_access(int *buf, int n)
{
  for (int i = 0; i <= n; i++) {
    if (buf[i] != 0)
      return;
    buf[i] = 0;
  }
}

/*
void good_access(int *buf, int n)
{
  for (int i = 0; i < n; i++) {
    if (buf[i] != 0)
      return;
    buf[i] = 0;
  }
}
*/

void foo(int *buf)
{
  bad_access(buf, 100);
  // good_access(buf, 100);
}

void bar()
{
  int buf[100];
  foo(buf);
}

/*
void other_access(int *buf)
{
  int *p = buf;
  p++;
  int *op = p;
  *op = 0;
}

void access(int *buf, int n)
{
  int *p = buf;
  int i = 0;
  while (i <= n) {
    *p = 0;
    p++;
    i++;
  }
}

void main()
{
  int buf[100];
  access(buf, 100);
}
*/
