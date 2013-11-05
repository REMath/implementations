
// handling of multiple inheritance.

class PA
{
public:
  virtual int pa1() = 0;
  virtual int pa2() { return -1; } 
};

class A : public PA
{
public:
  virtual int a1() { return 0; }
  virtual int a2() = 0;
  int pa1() { return 1000; }
  int add() { return a1() + a2(); }
};

class B
{
public:
  virtual int b1() { return 2; }
  virtual int b2() { return 3; }
  // virtual int a1() { return 10000; }
};

class C : public A, public B
{
public:
  int a2() { return 4; }
  int b2() { return 5; }
  int pa2() { return 7; }
  virtual int c1() { return 8; }
};

class D : public A, public B
{
public:
  int a1() { return 20; }
  int a2() { return 21; }
  int b1() { return 22; }
  int b2() { return 23; }
};

void callPA(PA *pa)
{
  pa->pa1();
  pa->pa2();
}

void callA(A *a)
{
  a->a1();
  a->a2();
  a->add();
  a->pa2();
}

void callB(B *b)
{
  b->b1();
  b->b2();
}

void callC(C *c)
{
  c->pa1();
  c->pa2();
  c->add();
  c->a1();
  c->a2();
  c->b1();
  c->b2();
  c->c1();
  callA(c);
  callB(c);
}

void start()
{
  B b;
  C c;
  D d;
  callB(&b);
  callC(&c);
}
