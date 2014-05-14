
class A {
  int a0;
  int a1;
  virtual void meth0() {}
};

class B : public A {
  int b0;
  int b1;
};

class C : public B {
  int c0;
  int c1;
  void meth0() {}
  void meth1(int a) { return a; }
};

class D : public C {
  int d0;
  int d1;
  void meth0() {}
};

void foo(A *a, B *b, C *c, D *d, int e)
{
  a->meth0();
  b->meth0();
  c->meth0();
  d->meth0();
}
