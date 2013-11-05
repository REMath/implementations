
// handling of diamond inheritance with virtual base classes.

class A
{
public:
  virtual int getA() { return a; }
  int a;
};

class B1 : public virtual A
{
public:
  int getB1() { return a + b1; }
  int b1;
};

class B2 : public virtual A
{
public:
  int getB2() { return a + b2; }
  int b2;
};

class C : public B1, public B2
{
public:
  int c;
};

int start(C *c)
{
  return c->a + c->getA() + c->b1 + c->getB2() + c->c;
}
