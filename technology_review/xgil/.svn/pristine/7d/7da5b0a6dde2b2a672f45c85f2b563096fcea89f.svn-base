
struct str;

extern str s;
extern __typeof__(str) s2;

// BAD
__typeof__(str) s3;

extern int x;

void foo()
{
  extern int x;
  static int y = 1;
}

int x = 0;

void bar()
{
  int x = 0;
  {
    int x = 1;
    x = 2;
  }
  x = 3;
}

static int z;

static int stat_stat()
{
  static int y = x;
  static int y2 = z;
  {
    // currently broken.
    static int y = x;
    return y;
  }
}

static int y;
