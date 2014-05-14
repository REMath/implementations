
// handling of diamond inheritance.

class A
{
public:
  virtual int getA() { return a; }
  int a;
};

class B1 : public A
{
public:
  int getB1() { return b1; }
  int b1;
};

class B2 : public A
{
public:
  int getB2() { return b2; }
  int b2;
};

class C : public B1, public B2
{
public:
  int c;
};

int start(C *c)
{
  return c->b1 + c->getB2() + c->c;
}
