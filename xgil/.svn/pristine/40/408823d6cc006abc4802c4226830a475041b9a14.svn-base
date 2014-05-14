
#include "../sixgill.h"

// handling of enums

struct str {
  enum  {
    FOO,
    BAR
  };

  invariant(type == FOO)
  int type;

  postcondition(return == BAR)
  int fun() { return BAR; }
};

void foo(str *s) {}
