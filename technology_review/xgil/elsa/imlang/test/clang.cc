
struct str {
  int a;
  int b;
};

struct str2 : str {
  int c;
  int d;
  str2();
};

str2::str2()
  : c(0), d(1)
{}

struct str3 : str2 {
  int e;
  int f;
};

struct str4 : str2 {
  int g;
  int h;
  str4(const str4 &o);
  ~str4();
};

str4::str4(const str4 &o)
  : str2(o)
{
  g = o.g;
  h = o.h;
}

struct str gs;

void foo(struct str xs, struct str2 xs2, struct str4 xs4)
{
  struct str s;
  s = xs;
  struct str2 s2 = xs2;
  struct str3 s3;
  struct str4 s4 = xs4;
}
