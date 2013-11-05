
#include "../sixgill.h"

// handling of enums

struct str {
  enum {
    FOO,
    BAR
  };

  invariant(type == FOO)
  int type;
};

int foo(struct str *s) { return FOO; }
