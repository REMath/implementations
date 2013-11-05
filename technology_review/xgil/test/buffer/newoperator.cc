
struct str {
  int a;
  int b;
};

void foo()
{
  str *s = new str();
  char *v = (char *) s;
  for (int i = 0; i < sizeof(str); i++)
    v[i] = 0;
}

void bar()
{
  int *ptr = new int[200];
  for (int i = 0; i < 200; i++)
    ptr[i] = 0;
}
