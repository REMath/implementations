
#include "gc.h"
#include "../sixgill.h"

struct Base {
  invariant(gcsafe(obj))
  JSObject *obj;
  JSObject *obj2;
};

void foo(Base *b)
{
  js_GC();
  b->obj->f = 0;
  b->obj2->f = 0;
}
