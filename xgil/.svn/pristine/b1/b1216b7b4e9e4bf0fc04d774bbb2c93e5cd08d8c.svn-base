// trcptr.cc            see license.txt for copyright and terms of use
// test rcptr module

#include "rcptr.h"        // module to test
#include <stdio.h>        // printf

// a simple class to play with
class Foo {
public:
  static int count;    // # of Foos there are
  int x;
  int refCt;

public:
  Foo(int a);
  ~Foo();
  
  void incRefCt() { refCt++; }
  void decRefCt();
};

int Foo::count = 0;

Foo::Foo(int ax)
  : x(ax), refCt(0)
{
  printf("created Foo at %p\n", this);
  count++;
}

Foo::~Foo()
{
  printf("destroying Foo at %p (refct=%d)\n", this, refCt);
  count--;
}

void Foo::decRefCt()
{
  if (--refCt == 0) {
    delete this;
  }
}


void printFoo(Foo *f)
{
  printf("Foo at %p, x=%d, refct=%d\n",
         f, f? f->x : 0, f? f->refCt : 0);
}

void printFooC(Foo const *f)
{
  printf("const Foo at %p, x=%d, refct=%d\n", 
         f, f? f->x : 0, f? f->refCt : 0);
}

void printInt(int x)
{
  printf("int x is %d\n", x);
}


// make it, forget to free it
void test1()
{
  printf("----------- test1 -----------\n");
  RCPtr<Foo> f;
  f = new Foo(4);
}

// access all of the operators as non-const
void test2()
{
  printf("----------- test2 -----------\n");
  RCPtr<Foo> f(new Foo(6));

  printFoo(f);
  (*f).x = 9;
  f->x = 12;
}

// access all of the operators as const
void test3()
{
  printf("----------- test3 -----------\n");
  RCPtr<Foo> f(new Foo(8));
  RCPtr<Foo> const &g = f;

  printFooC(g);
  printInt((*g).x);      // egcs-1.1.2 allows this for non-const operator fn!!!
  printInt(g->x);
}

// test exchange of ownership
void test4()
{
  printf("----------- test4 -----------\n");
  //RCPtr<Foo> f = new Foo(3);     // egcs-1.1.2 does the wrong thing here
  RCPtr<Foo> f(new Foo(3));
  RCPtr<Foo> g;
  g = f;
  f = NULL;
  printFoo(f);    // should be null
  f = g;
  g = NULL;
  printFoo(g);    // should be null
}

// test several things pointing at same obj
void test5()
{
  printf("----------- test5 -----------\n");
  RCPtr<Foo> f = new Foo(3);
  RCPtr<Foo> g = f;
  printFoo(f);
  g = NULL;
  printFoo(f);
}



int main()
{
  test1();
  test2();
  test3();
  test4();
  test5();
  
  printf("%d Foos leaked\n", Foo::count);
  return Foo::count;
}
