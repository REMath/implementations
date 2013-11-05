
#include "gc.h"

using namespace js;

void good(JSContext *cx, JSObject *base, JSObject **pobject)
{
  AutoRooter<JSObject> root(cx, &base);
  js_GC();
  *pobject = base;
}

void bad(JSContext *cx, JSObject *base, JSObject **pobject)
{
  *pobject = base;
  js_GC();
}

void caller(JSContext *cx, JSObject *base)
{
  JSObject *obj;
  if (base) {
    good(cx, base, &obj);
    obj->f = 0;
  } else {
    bad(cx, base, &obj);
    obj->f = 0;
  }
}
