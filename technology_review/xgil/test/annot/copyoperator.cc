
#include "../sixgill.h"

// default copy operators not allowed in structs within unions.

class HasAssignmentOperator {
 public:
  int x;
};

struct OtherStruct {
  int a;
  union {
    HasAssignmentOperator b;
    int c;
  };
};

precondition(s->a == s->b.x)
void UseOtherStruct(OtherStruct *s, HasAssignmentOperator w)
{
  s->b = w;
}
