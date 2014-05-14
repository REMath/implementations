
struct JSObject { int f; };
void js_GC() {}

void callGC(bool when) {
  if (when)
    js_GC();
}

struct Heap {
  JSObject *obj;
};

void other(JSObject *obj)
{
  obj->f = 0;
}

void copy1(Heap *h)
{
  JSObject *obj = h->obj;
  callGC(true);
  other(obj);
}

void copy2(Heap *h, Heap *h2)
{
  JSObject *obj = h->obj;
  callGC(true);
  h2->obj = obj;
}

JSObject* copy3(Heap *h)
{
  JSObject *obj = h->obj;
  callGC(true);
  return obj;
}

void caller(Heap *h)
{
  JSObject *obj = copy3(h);
  obj->f = 0;
}
