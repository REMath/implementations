
struct JSObject { int f; };
void js_GC() {}

void root_arg(JSObject *obj, JSObject *random)
{
  obj = random;
  JSObject *other1 = obj;
  js_GC();
  JSObject *other2 = obj;
  other1->f = 0;
  other2->f = 0;
}
