
#include "gc.h"

using namespace js;

void bad(JSObject *obj)
{
  js_GC();
  obj->f = 0;
}

void other_bad(JSContext *cx, JSObject *obj)
{
  {
    AutoRooter<JSObject> root(cx, &obj);
    obj->f = 0;
  }
  js_GC();
  obj->f = 0;
}

void good(JSContext *cx, JSObject *obj)
{
  AutoRooter<JSObject> root(cx, &obj);
  js_GC();
  obj->f = 0;
}

  /*
void split(JSContext *cx, JSObject *obj)
{
  AutoRooterVar<JSObject> obj2(cx, obj);
  js_GC();

  obj->f = 0;
  obj2->f = 0;
}

void other_split(JSContext *cx, JSObject *obj)
{
  AutoRooterVar<JSObject> obj2(cx, obj);
  js_GC();

  bad(obj2);
}
  */
