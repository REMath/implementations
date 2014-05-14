
struct str {
  int a;
  int b;
  int c;
};

void bar(void *v, int size)
{
  int int_size = size >> 2;

  int *np = (int*) v;
  for (int i = 0; i < int_size; i++)
    np[i] = 0;
}

void foo()
{
  struct str s;
  bar(&s, sizeof(s));
}
