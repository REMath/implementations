
// basic integer overflow testing.

typedef unsigned int u32;

void* malloc(u32);

void good_foo(u32 x, u32 y)
{
  if (x + y < x)
    return;

  void *buf = malloc(x + y);
}

void bad_foo(u32 x, u32 y)
{
  void *buf = malloc(x + y);
}

void main(u32 x, u32 y)
{
  int z = x;

  if (x == -1)
    return;
  if (x == z)
    return;

  good_foo(x, y);
  bad_foo(x, y);
}
