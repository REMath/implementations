
int h = 0;
int *g = &h;

struct str { int a; int b; };

void foo(int *x, int *y)
{
  x = y;
  *x = 2 + 3;

  struct str s0;
  struct str s1;
  s0 = s1;
}

void test_glob(int *x)
{
  g = x;

  foo(x, x);
}

void bar(int *x, int *y, int z)
{
  if (z) {
    x = y;
  }
  *x = 0;
}

int baz(int x)
{
  if (x == 0)
    return 0;
  if (x == 1)
    return 1;
  return 2;
}

int builtin_test(int x)
{
  if (__builtin_expect(++x == 0, 1))
    return 0;
  return 1;
}

int cascade(int x, int y, int z)
{
  int res;
  if (x)
    return 0;
  if (y)
    return 1;
  res = 2;
  if (z)
    res = 3;
  return res * res;
}

void coerce(long x, short z)
{
  int *y = (int*) x;
  *y = z;
}
