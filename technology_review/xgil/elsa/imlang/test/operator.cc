
// builtin operators

class A
{
public:
  int a;
  A& operator= (const A &o) { a = o.a; }
};

class B : A
{
public:
  int b;
};

/*
void foo(A a, B b)
{
  A tmpa = a;
  B tmpb = b;
}
*/
