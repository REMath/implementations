
// anonymous structures and fields.

/*
typedef struct {
  int a;
  int b;
} blargh;

struct {
  int c;
  int d;
} anon_str0;

struct {
  int e;
  int f;
} anon_str1;
*/

struct outer {
  union {
    struct {
      int a;
      int b;
    };
    double c;
  };
  int d;
};

void foo(struct outer o)
{
  o.a = o.b;
  o.c = (double) o.d;
}

class wtf {
  union {
    int e;
    int f;
  };
  int get_e_plus_f() { return e + f; }
};
