
#include "../sixgill.h"

// named and unnamed anonymous structures

struct invariant(a >= b) str0 {
  int a;
  union {
    // can't put invariants on unions.
    int b;
    int c;
  };
};

int foo0(str0 *s) { return s->b; }

struct str1 {
  struct {
    invariant(a >= b)
    int a;
    int b;
  } first, second;
};

postcondition(return == s->second.b)
int foo1(str1 *s) { return s->second.b; }
