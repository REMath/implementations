
// test __builtin_offsetof and rfld

struct lstr {
  int a;
  int b;
};

struct str {
  int x;
  int y;
  lstr ls;
};

void borken()
{
  // test that we don't parse __builtin_offsetof with a bogus offset.
  unsigned n = __builtin_offsetof(struct str, 1 + 2);
}

str* get_bstr(int *pb) {
 return ({
  const typeof( ((struct str *)0)->ls.b ) *__mptr = (pb);
  (struct str *)( (char *)__mptr -
                  __builtin_offsetof(struct str, ls.b) );
 });
}
