// demo.h
// *** DO NOT EDIT ***
// generated automatically by astgen, from demo.ast

#ifndef DEMO_H
#define DEMO_H

#include "asthelp.h"        // helpers for generated code

// fwd decls
class Root;
class A;
class A_one;
class A_two;
class B;
class B_one;
class B_two;


// *** DO NOT EDIT ***
class Root {
public:      // data
  A *a;
  B *b;

public:      // funcs
  Root(A *_a, B *_b) : a(_a), b(_b) {
  }
  ~Root();

  char const *kindName() const { return "Root"; }

  Root *clone() const;

  void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

};



// *** DO NOT EDIT ***
class A {
public:      // data

public:      // funcs
  A() {
  }
  virtual ~A();

  enum Kind { A_ONE, A_TWO, NUM_KINDS };
  virtual Kind kind() const = 0;

  static char const * const kindNames[NUM_KINDS];
  char const *kindName() const { return kindNames[kind()]; }

  DECL_AST_DOWNCASTS(A_one, A_ONE)
  DECL_AST_DOWNCASTS(A_two, A_TWO)

  virtual A* clone() const=0;

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

};

class A_one : public A {
public:      // data
  string name;

public:      // funcs
  A_one(string _name) : A(), name(_name) {
  }
  virtual ~A_one();

  virtual Kind kind() const { return A_ONE; }
  enum { TYPE_TAG = A_ONE };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual A_one *clone() const;

};

class A_two : public A {
public:      // data
  B *b;

public:      // funcs
  A_two(B *_b) : A(), b(_b) {
  }
  virtual ~A_two();

  virtual Kind kind() const { return A_TWO; }
  enum { TYPE_TAG = A_TWO };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual A_two *clone() const;

};



// *** DO NOT EDIT ***
class B {
public:      // data
  string name;

public:      // funcs
  B(string _name) : name(_name), x( 0) {
  }
  virtual ~B();

  enum Kind { B_ONE, B_TWO, NUM_KINDS };
  virtual Kind kind() const = 0;

  static char const * const kindNames[NUM_KINDS];
  char const *kindName() const { return kindNames[kind()]; }

  DECL_AST_DOWNCASTS(B_one, B_ONE)
  DECL_AST_DOWNCASTS(B_two, B_TWO)

  virtual B* clone() const=0;

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  public:  int x ;
};

class B_one : public B {
public:      // data
  int y;

public:      // funcs
  B_one(string _name, int _y) : B(_name), y(_y) {
  }
  virtual ~B_one();

  virtual Kind kind() const { return B_ONE; }
  enum { TYPE_TAG = B_ONE };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual B_one *clone() const;

};

class B_two : public B {
public:      // data
  char c;

public:      // funcs
  B_two(string _name, char _c) : B(_name), c(_c) {
  }
  virtual ~B_two();

  virtual Kind kind() const { return B_TWO; }
  enum { TYPE_TAG = B_TWO };

  virtual void debugPrint(ostream &os, int indent, char const *subtreeName = "tree") const;

  virtual B_two *clone() const;

};



#endif // DEMO_H
