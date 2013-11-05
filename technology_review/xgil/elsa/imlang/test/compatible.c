
// type compatibility

struct str {
  int a;
  int b;
};

void foo(int x)
{
  struct str s = x;
}



