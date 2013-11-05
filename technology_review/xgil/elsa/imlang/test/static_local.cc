
int foo()
{
  static int x = 0;
  return x;
}

int bar()
{
  static int x = 1;
  return x;
}

static int baz()
{
  static int x = 2;
  return x;
}
