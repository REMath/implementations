// demo.cc
// *** DO NOT EDIT ***
// generated automatically by astgen, from demo.ast

#include "gendoc/demo.h"      // this module


// ------------------ Root -------------------
// *** DO NOT EDIT ***
Root::~Root()
{
  delete a;
  delete b;
}

void Root::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, Root);

  PRINT_SUBTREE(a);
  PRINT_SUBTREE(b);
}

Root *Root::clone() const
{
  Root *ret = new Root(
    a? a->clone() : NULL,
    b? b->clone() : NULL
  );
  return ret;
}


// ------------------ A -------------------
// *** DO NOT EDIT ***
A::~A()
{
}

char const * const A::kindNames[A::NUM_KINDS] = {
  "A_one",
  "A_two",
};

void A::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
}

DEFN_AST_DOWNCASTS(A, A_one, A_ONE)

A_one::~A_one()
{
}

void A_one::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, A_one);

  A::debugPrint(os, indent, subtreeName);

  PRINT_STRING(name);
}

A_one *A_one::clone() const
{
  A_one *ret = new A_one(
    name
  );
  return ret;
}

DEFN_AST_DOWNCASTS(A, A_two, A_TWO)

A_two::~A_two()
{
  delete b;
}

void A_two::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, A_two);

  A::debugPrint(os, indent, subtreeName);

  PRINT_SUBTREE(b);
}

A_two *A_two::clone() const
{
  A_two *ret = new A_two(
    b? b->clone() : NULL
  );
  return ret;
}


// ------------------ B -------------------
// *** DO NOT EDIT ***
B::~B()
{
}

char const * const B::kindNames[B::NUM_KINDS] = {
  "B_one",
  "B_two",
};

void B::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_STRING(name);
}

DEFN_AST_DOWNCASTS(B, B_one, B_ONE)

B_one::~B_one()
{
}

void B_one::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, B_one);

  B::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(y);
}

B_one *B_one::clone() const
{
  B_one *ret = new B_one(
    name,
    y
  );
  return ret;
}

DEFN_AST_DOWNCASTS(B, B_two, B_TWO)

B_two::~B_two()
{
}

void B_two::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  PRINT_HEADER(subtreeName, B_two);

  B::debugPrint(os, indent, subtreeName);

  PRINT_GENERIC(c);
}

B_two *B_two::clone() const
{
  B_two *ret = new B_two(
    name,
    c
  );
  return ret;
}




