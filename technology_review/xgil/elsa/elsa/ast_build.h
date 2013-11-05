// ast_build.h
// some utilities for constructing fragments of the C++ AST

#ifndef AST_BUILD_H
#define AST_BUILD_H

#include "cc_ast.h"      // C++ AST

// wrap an expression in a list
FakeList<ArgExpression> *makeExprList1(Expression *e);

// wrap a pair of expressions in a list
FakeList<ArgExpression> *makeExprList2(Expression *e1, Expression *e2);

#endif // AST_BUILD_H
