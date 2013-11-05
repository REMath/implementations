
#include "../sixgill.h"

typedef struct str {
  invariant(skip_inference())
  int *buf;
} str;

void foo1(str *s) { s->buf[10] = 0; }
void foo2(str *s) { s->buf[20] = 0; }

void bar1()
{
  int x[11];
  str s = { x };
  foo1(&s);
}

void bar2()
{
  int x[21];
  str s = { x };
  foo2(&s);
}
