// gramast.h            see license.txt for copyright and terms of use
// declarations for the grammar AST

#ifndef __GRAMAST_H
#define __GRAMAST_H

#error This file is now obsolete.  Use gramast.ast.gen.h instead.

#include "ast.h"       // basic ast stuff
#include "str.h"       // string


// node type codes
enum ASTTypeCode {
  // ---- leaves ----
  // tokens
  AST_INTEGER=1,         // ASTIntLeaf
  AST_STRING,            // ASTStringLeaf
  AST_NAME,              // ASTNameLeaf

  // ---- internal nodes ----
  // grammar tree components
  AST_TOPLEVEL,          // list of toplevel forms

  AST_TERMINALS,         // list of terminal declarations
  AST_TERMDECL,          // terminal: numeric-code, aliases
  AST_ALIASES,           // list of terminal aliases
  
  AST_NONTERM,           // nonterminal: ntname, (form or ntbody)
  AST_NTBODY,            // list of nonterminal body elements
  AST_NTNAME,            // name, [baseclasses]
  AST_BASECLASSES,       // list of base class nonterminal names

  AST_ATTR,              // attribute decl: name
  AST_FORM,              // form: rhs, [formbody]
  AST_RHSALTS,           // list of ALT_RHSs
  AST_RHS,               // list of RHS elements
  AST_TAGGEDNAME,        // tagged name: tag, name
  AST_TAGGEDSTRING,      // tagged string: tag, string

  AST_FORMBODY,          // list of form body elements
  AST_FORMGROUPBODY,     // list of formGroup body elements

  AST_ACTION,            // action: attr, expr
  AST_CONDITION,         // condition: expr
  AST_FUNDECL,           // fundecl: name, body
  AST_FUNCTION,          // fun: name, body
  AST_FUNEXPR,           // fun: name, expr-body

  AST_TREENODEBASE,      // base class: string
  AST_TREECOMPARE,       // name1, name2, expr
  AST_DECLARATION,       // decl: decl body
  
  AST_LITERALCODE,       // code-tag, body
  AST_NAMEDLITERALCODE,  // code-tag, body, name

  // attribute-expression components
  EXP_ATTRREF,           // reference to an attribute
  EXP_FNCALL,            // function call
  EXP_LIST,              // expression list

  EXP_NEGATE,            // unary operators
  EXP_NOT,

  EXP_MULT,              // binary operators
  EXP_DIV,
  EXP_MOD,
  EXP_PLUS,
  EXP_MINUS,
  EXP_LT,
  EXP_GT,
  EXP_LTE,
  EXP_GTE,
  EXP_EQ,
  EXP_NEQ,
  EXP_AND,
  EXP_OR,

  EXP_COND,              // ternary operator
  
  NUM_AST_CODES          // plus one, actually
};

                                 
// map type to descriptive string
string astTypeToString(int type);


// why did I differentiate between string and name??
typedef ASTSimpleLeaf<int, AST_INTEGER> ASTIntLeaf;
typedef ASTSimpleLeaf<string, AST_STRING> ASTStringLeaf;
typedef ASTSimpleLeaf<string, AST_NAME> ASTNameLeaf;


#endif // __GRAMAST_H
