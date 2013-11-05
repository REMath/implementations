
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
  int a[10] = { 1, 2, [5 ... 6] = 3 };
  struct str s = (str) { .s1 = { 1, 2 }, .s2.a = 3, .x = 4, 5 };
  int m[2][2][2] = { [0][0][0] = 1 };
  char data[20] = "foobar";
}

