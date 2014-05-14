
#include "../sixgill.h"

struct str {
  int a;
  int b;
};

precondition(ubound(s) >= 10)
void foo(str *s) {}

precondition(ubound(s) >= 10)
void bar(char const *s) {}
