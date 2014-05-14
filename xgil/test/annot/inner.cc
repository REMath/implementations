
#include "../sixgill.h"

// handle annotations for inner structures.

struct Outer
{
  typedef struct Inner {
    int a;
  } Inner;

  precondition(inner->a == 0)
  void function(Inner *inner) {}
};

