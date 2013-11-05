
#include "../sixgill.h"

// use of sizeof in annotations

struct str {
  int a;
  int b;
};

postcondition(return == sizeof(str))
int size_of_str() { return 8; }
