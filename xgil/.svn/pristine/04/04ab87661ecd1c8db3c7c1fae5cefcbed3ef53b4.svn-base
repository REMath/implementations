
#include "../sixgill.h"

// use of sizeof in annotations

struct str {
  int a;
  int b;
};

// sizeof doesn't work in C right now on unknown types, and is broken
// anyways on types that have been named but not defined.
postcondition(return == sizeof(struct str))
int size_of_str() { return 8; }
