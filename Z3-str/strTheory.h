#ifndef __strTheory_H
#define __strTheory_H 1

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <memory.h>
#include <unistd.h>
#include <assert.h>
#include <map>
#include <list>
#include <stack>
#include <string>
#include <sstream>
#include <algorithm>
#include <getopt.h>
#include <utility>

#include "z3.h"

#define unCstrStrMaxLen  7
#define str2Int_MinInt  -50
#define str2Int_MaxInt   50

#ifdef DEBUGLOG
  #define __debugPrint(_fp, _format, ...) { fprintf( (_fp), (_format), ##__VA_ARGS__); fflush( (_fp) ); }
  #define printZ3Node(t, n) {__printZ3Node( (t), (n));}
#else
  #define __debugPrint(_fp, _format, ...) {}
  #define printZ3Node(t, n) {}
#endif

/**
 * Theory specific data-structures.
 */
typedef struct _PATheoryData
{
    Z3_sort String;
    Z3_func_decl Compare;
    Z3_func_decl Concat;
    Z3_func_decl Length;
    Z3_func_decl SubString;
    Z3_func_decl Indexof;
    Z3_func_decl Contains;
    Z3_func_decl Replace;

    Z3_func_decl Str2Int;  // assume the argument is always convertible
    Z3_func_decl Str2Real;

//    Z3_func_decl OTHERVALUE;
} PATheoryData;


typedef enum
{
  my_Z3_ConstStr,    // 0
  my_Z3_Func,        // 1
  my_Z3_Num,         // 2
  my_Z3_Var,         // 3
  my_Z3_Str_Var,     // 4
  my_Z3_Int_Var,     // 5
  my_Z3_Quantifier,  // 6
  my_Z3_Unknown      // 7
} T_myZ3Type;


extern FILE * logFile;

//--------------------------------------------------
// Function Declaration
//--------------------------------------------------

Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty);

Z3_ast mk_bool_var(Z3_context ctx, const char * name);

Z3_ast mk_int_var(Z3_context ctx, const char * name);

Z3_ast mk_int(Z3_context ctx, int v);

Z3_ast my_mk_str_value(Z3_theory t, char const * str);

Z3_ast my_mk_str_var(Z3_theory t, char const * name);

Z3_ast my_mk_internal_string_var(Z3_theory t);

Z3_ast my_mk_breakDown_string_var(Z3_theory t);

Z3_ast mk_unary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x);

T_myZ3Type getNodeType(Z3_theory t, Z3_ast n);

Z3_ast mk_1_arg_app(Z3_context ctx, Z3_func_decl f, Z3_ast x);

Z3_ast mk_2_arg_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y);

Z3_ast mk_3_arg_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y, Z3_ast z);

Z3_ast mk_2_and(Z3_theory t, Z3_ast and1, Z3_ast and2);

Z3_ast mk_2_add(Z3_theory t, Z3_ast add1, Z3_ast add2);

Z3_ast mk_3_and(Z3_theory t, Z3_ast and1, Z3_ast and2, Z3_ast and3);

Z3_ast mk_4_and(Z3_theory t, Z3_ast and1, Z3_ast and2, Z3_ast and3, Z3_ast and4);

Z3_ast mk_5_and(Z3_theory t, Z3_ast and1, Z3_ast and2, Z3_ast and3, Z3_ast and4, Z3_ast and5);

Z3_ast my_mk_str_compare(Z3_theory t, Z3_ast n1, Z3_ast n2);

Z3_ast mk_concat(Z3_theory t, Z3_ast n1, Z3_ast n2);

bool isTwoStrEqual(std::string str1, std::string str2);

void printContext(Z3_context ctx, int line, char *title);

int get_sizeof_eq_class(Z3_theory t, Z3_ast n);

void print_eq_class(Z3_theory t, Z3_ast n);

void __printZ3Node(Z3_theory t, Z3_ast node);

Z3_ast get_eq_value_from_ctx(Z3_theory t, Z3_ast n);

Z3_ast get_eqc_value(Z3_theory t, Z3_ast n);

int isNodeInNodeList(Z3_ast node, std::list<Z3_ast> * nodeList);

inline bool isConcatFunc(Z3_theory t, Z3_ast n);

void init_strLengthCstr(Z3_theory t);

void collect_init_strVar_strEq(Z3_theory t);

std::string getConstStrValue(Z3_theory t, Z3_ast n);

Z3_lbool Compare(Z3_theory t, Z3_ast n1, Z3_ast n2);

Z3_ast Concat(Z3_theory t, Z3_ast n1, Z3_ast n2);

void reduceCmpConcat_3(Z3_theory t, Z3_ast n1, Z3_ast n2, Z3_ast * result);

void reduceCmpConcat_1(Z3_theory t, Z3_ast n1, Z3_ast n2, Z3_ast * result);

int isCmpConcatPattern2(Z3_theory t, Z3_ast arg1, Z3_ast arg2);

void reduceCmpConcat_2(Z3_theory t, Z3_ast n1, Z3_ast n2, Z3_ast * result);

int isAppAlreadyReduced(Z3_func_decl appType, Z3_ast arg1, Z3_ast arg2);

void apply_eq_in_eqc(Z3_theory t, Z3_ast n, Z3_ast v);

void apply_eq_in_parents(Z3_theory t, Z3_ast n, Z3_ast v);

void simplifyConcat_constStr(Z3_theory t, Z3_ast nn, Z3_ast eq_const);

Z3_ast getStrAssignFromCtx(Z3_theory t);

void apply_eq_axiom_for_compare_parents(Z3_theory t, Z3_ast n, Z3_ast v);

void solve_concat_eq_str(Z3_theory t, Z3_ast concatAst, Z3_ast constStr);

void solve_var_eq_constStr(Z3_theory t, Z3_ast var, Z3_ast constStr);

void constraintWeakStrVar(Z3_theory t, Z3_ast n, std::map<Z3_ast, int> * constrainted_map);

int getVarCountInAst(Z3_theory t, Z3_ast n);

void getStrVarsInNode(Z3_theory t, Z3_ast node, std::map<Z3_ast, int> & astList);

void getconstStrAstsInNode(Z3_theory t, Z3_ast node, std::list<Z3_ast> & astList);

bool areTwoNodesInSameEqc(Z3_theory t, Z3_ast n1, Z3_ast n2);

bool canTwoNodesEq(Z3_theory t, Z3_ast n1, Z3_ast n2);

int simplifyConcatEq(Z3_theory t, Z3_ast nn1, Z3_ast nn2, int duplicateCheck = 1);

void cb_new_eq(Z3_theory t, Z3_ast n1, Z3_ast n2);

Z3_bool cb_final_check(Z3_theory t);

Z3_bool cb_reduce_eq(Z3_theory t, Z3_ast s_1, Z3_ast s_2, Z3_ast * r);

void cb_init_search(Z3_theory t);

Z3_bool cb_reduce_app(Z3_theory t, Z3_func_decl d, unsigned n, Z3_ast const * args, Z3_ast * result);

void cb_push(Z3_theory t);

void cb_pop(Z3_theory t);

void cb_reset(Z3_theory t);

void cb_restart(Z3_theory t);

void cb_new_relevant(Z3_theory t, Z3_ast n);

void cb_delete(Z3_theory t);

int check(Z3_context ctx);

void cb_new_elem(Z3_theory t, Z3_ast n);

Z3_theory mk_pa_theory(Z3_context ctx);

void throw_z3_error(Z3_context ctx, Z3_error_code c);

Z3_context mk_context_custom(Z3_config cfg);

Z3_context mk_my_context();

void classifyAstByType(Z3_theory t, Z3_ast node, std::map<Z3_ast, int> & varMap, std::map<Z3_ast, int> & concatMap);

void getStrVarsInCtx(Z3_theory t, Z3_ast node, std::map<Z3_ast, int> & varMap, std::map<std::pair<Z3_ast, Z3_ast>, int> & eqAstMap);

Z3_ast axiomForFreeVar(Z3_theory t, Z3_ast n);

void basicStrVarAxiom(Z3_theory t, Z3_ast vNode, int line);

void basicConcatAxiom(Z3_theory t, Z3_ast vNode, int line);

Z3_ast getMostLeftNodeInConcat(Z3_theory t, Z3_ast node);

Z3_ast getMostRightNodeInConcat(Z3_theory t, Z3_ast node);

int ctxDepAnalysis(Z3_theory t, std::map<Z3_ast, int> & varAppearMap,
    std::map<Z3_ast, int> & concatMap,
    std::map<Z3_ast, Z3_ast> & aliasIndexMap, std::map<Z3_ast, Z3_ast> & var_eq_constStr_map,
    std::map<Z3_ast, std::map<Z3_ast, int> > & var_eq_concat_map,
    std::map<Z3_ast, Z3_ast> & concat_eq_constStr_map,
    std::map<Z3_ast, std::map<Z3_ast, int> > & concat_eq_concat_map,
    std::map<Z3_ast, int> & freeVarMap, std::map<Z3_ast, std::map<Z3_ast, int> > & depMap);

Z3_ast mk_length(Z3_theory t, Z3_ast n);

void strEqLengthAxiom(Z3_theory t, Z3_ast varAst, Z3_ast strAst, int line);

void addAxiom(Z3_theory t, Z3_ast toAssert, int line, bool display = true);

void basicStrVarAxiom(Z3_theory t, Z3_ast vNode, int line);

int countConcatInNode(Z3_theory t, Z3_ast node);

void handleNodesEqual(Z3_theory t, Z3_ast v1, Z3_ast v2);

int canConcatEqStr(Z3_theory t, Z3_ast concat, std::string str);

int canConcatEqConcat(Z3_theory t, Z3_ast concat1, Z3_ast concat2);

void doubleCheckForNotContain(Z3_theory t);

#endif

