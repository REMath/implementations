
void access(int *buf, int n, int i)
{
  if (i <= n)
    buf[i] = 0;
}

void foo(int *buf, int n, int i)
{
  access(buf, n, i);
}

/*
void bar(int i)
{
  int buf[100];

  i--;
  foo(buf, 100, i);
}
*/

void bad_bar_one()
{
  int buf[50];
  foo(buf, 50, 50);
}

void good_bar_two(int i)
{
  int buf[50];
  if (i <= 50)
    foo(buf, 50, i - 1);
}
