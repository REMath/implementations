
// basic end pointer example.

int foo(char *buf, char *end, int c)
{
  while (buf < end) {
    if (*buf == c)
      return 1;
    buf++;
  }
  return 0;
}

void bar()
{
  char array[1000];
  char *endptr = &array[sizeof array];

  foo(array, endptr, 23);
}
