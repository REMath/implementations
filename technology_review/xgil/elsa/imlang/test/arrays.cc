
/*
int foo()
{
  int x[10];
  // x += 3;
  x[3] = 0;

  int a = x[3];
  int *b = &x[3];

  int &y = x[0];
  int *z = x;

  int *w = x;

  char c = "fubar"[4];
}

int multi()
{
  int x[10][20];
  x[10][20] = 1;
}

int passee(int x[])
{
  x[10] = 3;
}

int passer()
{
  int y[20];
  passee(y);
}
*/

struct str {
  int a;
  int b;
  str() {}
  ~str() {}
  str(int _a, int _b) : a(_a), b(_b) {}
  void blech(int a, int b) {}
  static void blargh() {}
};

int str_array()
{
  str arr[100];

  str *sarr = new str[50];
  delete[] sarr;

  str *mstr = new str(1, 2);
  delete mstr;

  new str(3, 4);
  int wtf = (new str(5, 6))->a;
}

