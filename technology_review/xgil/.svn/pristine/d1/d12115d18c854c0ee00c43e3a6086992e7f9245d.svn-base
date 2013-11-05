
// see calls.cc for more funptrs. this tests address-of.

void indir();

void foo(void (*fn)()) {
  (*****fn)();
}

void bar()
{
  foo(indir);
  foo(&indir);
}

typedef void (*fnptr)();

fnptr make_fnptr();

// this is a weird one.
void blargh()
{
  make_fnptr()();
}
