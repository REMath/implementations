// gramast.cc            see license.txt for copyright and terms of use
// code for gramast.h

#error This module is obsolete; use gramast.gen.{cc,h} instead.

#include "gramast.h"      // this module
#include "macros.h"       // STATIC_ASSERT

string astTypeToString(int type)
{
  static struct {
    int code;
    char const *name;
  } const arr[] = {
    #define N(code) { code, #code },
    N(AST_INTEGER)
    N(AST_STRING)
    N(AST_NAME)
    
    N(AST_TOPLEVEL)
    N(AST_TERMINALS)
    N(AST_TERMDECL)
    N(AST_ALIASES)
    N(AST_NONTERM)
    N(AST_NTBODY)
    N(AST_NTNAME)
    N(AST_BASECLASSES)
    N(AST_ATTR)
    N(AST_FORM)
    N(AST_RHSALTS)
    N(AST_RHS)
    N(AST_TAGGEDNAME)
    N(AST_TAGGEDSTRING)
    N(AST_FORMBODY)
    N(AST_FORMGROUPBODY)
    N(AST_ACTION)
    N(AST_CONDITION)
    N(AST_FUNDECL)
    N(AST_FUNCTION)
    N(AST_FUNEXPR)
    N(AST_TREENODEBASE)
    N(AST_TREECOMPARE)
    N(AST_DECLARATION)
    N(AST_LITERALCODE)
    N(AST_NAMEDLITERALCODE)

    N(EXP_ATTRREF)
    N(EXP_FNCALL)
    N(EXP_LIST)
    N(EXP_NEGATE)
    N(EXP_NOT)
    N(EXP_MULT)
    N(EXP_DIV)
    N(EXP_MOD)
    N(EXP_PLUS)
    N(EXP_MINUS)
    N(EXP_LT)
    N(EXP_GT)
    N(EXP_LTE)
    N(EXP_GTE)
    N(EXP_EQ)
    N(EXP_NEQ)
    N(EXP_AND)
    N(EXP_OR)
    N(EXP_COND)
    #undef N
  };

  STATIC_ASSERT(TABLESIZE(arr) == NUM_AST_CODES-1);

  loopi(TABLESIZE(arr)) {
    if (arr[i].code == type) {
      return arr[i].name;
    }
  }
  
  xfailure("bad type code");
  return NULL;   // silence warning
}
