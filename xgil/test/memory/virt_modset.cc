
// modsets in the presence of virtual calls.

class A
{
public:
  int a;
  virtual int Set(int x) = 0;
};

class B : public A
{
public:
  int b;
  int Set(int x) { a = x; b = x; }
};

class C : public A
{
public:
  int c;
  int Set(int x) { c = x; }
};

void setter(A *a)
{
  a->Set(0);
}

void starter()
{
  B b;
  C c;
}
