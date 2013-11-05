
// Sixgill: Static assertion checker for C/C++ programs.
// Copyright (C) 2009-2010  Stanford University
// Author: Brian Hackett
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// C interface for interacting with CVC3. this is similar to the C interface
// supplied with CVC3 itself, with a few differences:
// 1. traps and dies on any exceptions encountered.
// 2. adds some interface functionality we need.
// 3. avoids some naming conflicts.
// 4. uses XIL opcodes where possible.
// 5. leaned down to just what we need.
// it would be nice to include the CVC3 headers directly; not doing this
// because we only want to interact with other systems through C interfaces
// (e.g. we override operator new and that interacts badly with std).

#ifndef CVC3_INTERFACE
#define CVC3_INTERFACE

#include <imlang/interface.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef void* CVC_VC;
typedef void* CVC_Exp;
typedef void* CVC_Op;
typedef void* CVC_Type;

// create/destroy a validity checker.
CVC_VC CVC_NewVC();
void CVC_DeleteVC(CVC_VC);

// push/pop the context on a VC.
void CVC_Push(CVC_VC);
void CVC_Pop(CVC_VC);

// add an assertion to a VC.
void CVC_Assert(CVC_VC, CVC_Exp exp);

// returns whether exp is valid in the VC's context.
int CVC_Query(CVC_VC, CVC_Exp exp);

// if a query returned not valid, get a concrete model for that result.
// size will receive the number of variables assigned to, vars will receive
// the variables assigned, vals will receive the values assigned to those vars.
// the model data persists until the next GetConcreteModel or Pop.
void CVC_GetConcreteModel(CVC_VC, long *psize,
                          CVC_Exp **pvars, CVC_Exp **pvals);

// get a string representation of the integer value of exp, according to the
// most recent concrete model. exp is a value which was stored in pvals.
const char* CVC_ExpModelInteger(CVC_Exp exp);

// if the context is inconsistent (Query returned valid on a false expression),
// store an unsat core in size/asserts. this requires a debug build of CVC3.
void CVC_Inconsistent(CVC_VC, long *psize, CVC_Exp **pexps);

// create primitive and function types.
CVC_Type CVC_TypeBool(CVC_VC);
CVC_Type CVC_TypeInt(CVC_VC);
CVC_Type CVC_TypeFunc(CVC_VC, CVC_Type ret, CVC_Type *args, int num_args);

// create uninterpreted functions. type must be a function type.
CVC_Op CVC_NewOp(CVC_VC, const char *name, CVC_Type type);

// create integer and boolean constants.
CVC_Exp CVC_ExpInt(CVC_VC, long value);
CVC_Exp CVC_ExpIntStr(CVC_VC, const char *str);
CVC_Exp CVC_ExpBool(CVC_VC, int value);

// create variables.
CVC_Exp CVC_ExpVar(CVC_VC, const char *name, CVC_Type type);

// create unops and binops. fails on unops/binops that can't be modelled exact.
CVC_Exp CVC_ExpUnop(CVC_VC, XIL_UnopKind unop, CVC_Exp exp);
CVC_Exp CVC_ExpBinop(CVC_VC, XIL_BinopKind binop,
                     CVC_Exp left_exp, CVC_Exp right_exp);

// create if-then-else expressions.
CVC_Exp CVC_ExpITE(CVC_VC, CVC_Exp _if, CVC_Exp _then, CVC_Exp _else);

// create function applications.
CVC_Exp CVC_ExpApply(CVC_VC, CVC_Op op, CVC_Exp *args, int num_args);

// print an expression to stdout.
void CVC_ExpPrint(CVC_VC, CVC_Exp exp);

// convert an expression to a string. the result is good until the next
// call to ExpToString.
const char* CVC_ExpToString(CVC_Exp exp);

// return whether exp is a constant integer.
bool CVC_ExpIsInteger(CVC_Exp exp);

#ifdef __cplusplus
}
#endif

#endif // CVC3_INTERFACE
