

class A {
public:
  int a0;
  int a1;
  A(int _a0, int _a1) : a0(_a0), a1(_a1) {}
  virtual ~A() {}
};

class B : public A {
public:
  int b0;
  int b1;
  B(int _b0, int _b1) : A(1, 2), b0(_b0), b1(_b1) {}
  // virtual ~B() {}
};

class C : public A {
public:
  int c0;
  int c1;
  C() : A(5, 6), c0(7), c1(8) {}
  // virtual ~C() {}
};

class D : public B, public C {
public:
  int d0;
  int d1;
  D() : B(9, 10), d0(11), d1(12) {}
};

void foo()
{
  D d;
}
