
struct bstr {
  int a;
  int b;
};

struct str {
  int x;
  int y;
  struct bstr s1;
  struct bstr s2;
};

void foo()
{
  struct str s;
  s = (struct str) { .s1 = { 1, 2 }, .s2.a = 3, .x = 4, 5 };
}
