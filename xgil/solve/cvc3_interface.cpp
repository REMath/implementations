
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

// implementation of the xgill interface with CVC3.

// only include our interface header and CVC3 headers --- need to be isolated
// from the remainder of the XGill headers.
#include "cvc3_interface.h"

#include <cvc3/vc.h>
#include <cvc3/command_line_flags.h>
#include <cvc3/theory_arith.h>

/////////////////////////////////////////////////////////////////////
// Utility
/////////////////////////////////////////////////////////////////////

// assertion macro as in util/assert.h
#define Assert(COND)                                            \
  do {                                                          \
    if (!(COND)) {                                              \
      FILE *log_file = XIL_GetLogFile();                        \
      fprintf(log_file, "%s: %d: %s: Assertion failed: '%s'\n", \
              __FILE__, __LINE__, __FUNCTION__, #COND);         \
      abort();                                                  \
    }                                                           \
  } while (0)

// macro to bail out whenever CVC3 generates an exception.
#define ExceptionFail(EX)  Assert(!"CVC3 Exception")

// get the VC from the handle we expose externally.
#define GetVC  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc

// translate between expr/type/op handles and the internal representation.
// this is based on the translation code from CVC3's C interface
// (it pretty much has to be since Expr/etc. declare CInterface as friends
// and the constructors we need are private).

class CInterface
{
public:
  static CVC3::Expr FromExp(CVC_Exp exp)
  {
    return CVC3::Expr((CVC3::ExprValue*)exp);
  }

  static CVC_Exp ToExp(const CVC3::Expr& exp)
  {
    if (!exp.d_expr) return NULL;
    exp.d_expr->incRefcount();
    return (CVC_Exp) exp.d_expr;
  }

  static CVC3::Type FromType(CVC_Type type)
  {
    return CVC3::Type(FromExp(type));
  }

  static CVC_Type ToType(const CVC3::Type& type)
  {
    return ToExp(type.getExpr());
  }
};

#define FromExp CInterface::FromExp
#define ToExp CInterface::ToExp
#define FromType CInterface::FromType
#define ToType CInterface::ToType

/////////////////////////////////////////////////////////////////////
// VC Operations
////////////////////////////////////////////////////////////////////

extern "C" CVC_VC CVC_NewVC()
{
  try {
    CVC3::CLFlags flags = CVC3::ValidityChecker::createFlags();
    return (CVC_VC) CVC3::ValidityChecker::create(flags);
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" void CVC_DeleteVC(CVC_VC vc)
{
  GetVC;
  try {
    delete cvc;
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" void CVC_Push(CVC_VC vc)
{
  GetVC;
  try {
    cvc->push();
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" void CVC_Pop(CVC_VC vc)
{
  GetVC;
  try {
    cvc->pop();
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" void CVC_Assert(CVC_VC vc, CVC_Exp exp)
{
  GetVC;
  try {
    cvc->assertFormula(FromExp(exp));
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" int CVC_Query(CVC_VC vc, CVC_Exp exp)
{
  GetVC;
  try {
    int valid = cvc->query(FromExp(exp));
    Assert(valid == 0 || valid == 1);
    return valid;
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

// arrays for returning assignment data.
static CVC_Exp *model_vars = NULL;
static CVC_Exp *model_vals = NULL;
long model_size = 0;

extern "C" void CVC_GetConcreteModel(CVC_VC vc, long *psize,
                                     CVC_Exp **pvars, CVC_Exp **pvals)
{
  GetVC;
  try {
    CVC3::ExprMap<CVC3::Expr> model;
    cvc->getConcreteModel(model);

    // make sure we have room to store the model.
    unsigned needed = sizeof(CVC_Exp) * model.size();
    model_vars = (CVC_Exp*) realloc(model_vars, needed);
    model_vals = (CVC_Exp*) realloc(model_vals, needed);
    model_size = model.size();

    unsigned n = 0;
    CVC3::ExprMap<CVC3::Expr>::iterator it = model.begin();
    CVC3::ExprMap<CVC3::Expr>::iterator end = model.end();
    for (; it != end; it++) {
      model_vars[n] = ToExp(it->first);
      model_vals[n] = ToExp(it->second);
      n++;
    }
    Assert(n == model.size());

    *psize = model.size();
    *pvars = model_vars;
    *pvals = model_vals;
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

// store the rational representation of exp into rat, according to the
// most recently generated model.
static bool ExpModelRational(const CVC3::Expr &exp, CVC3::Rational &rat)
{
  // usual case, the expression is already an integer. it would be nice if
  // this was the 'always' case (except with assignments for function symbols,
  // which shouldn't get here), but it is not.
  if (exp.isRational()) {
    rat = exp.getRational();
    return true;
  }

  if (isPlus(exp)) {
    if (!ExpModelRational(exp[0], rat))
      return false;
    for (int i = 1; i < exp.arity(); i++) {
      CVC3::Rational crat;
      if (!ExpModelRational(exp[i], crat))
        return false;
      rat += crat;
    }
    return true;
  }

  if (isMult(exp)) {
    if (!ExpModelRational(exp[0], rat))
      return false;
    for (int i = 1; i < exp.arity(); i++) {
      CVC3::Rational crat;
      if (!ExpModelRational(exp[i], crat))
        return false;
      rat *= crat;
    }
    return true;
  }

  // see if this is a key in the model we generated.
  for (long i = 0; i < model_size; i++) {
    if (model_vars[i] == ToExp(exp))
      return ExpModelRational(FromExp(model_vals[i]), rat);
  }

  // printf("ERROR: Unknown expression from model: %s\n",
  //        exp.toString().c_str());

  return false;
}

extern "C" const char* CVC_ExpModelInteger(CVC_Exp exp)
{
  try {
    CVC3::Expr nexp = FromExp(exp);
    static std::string tmp;

    CVC3::Rational rat;
    if (ExpModelRational(nexp, rat)) {
      tmp = rat.toString();
      return tmp.c_str();
    }
    return NULL;
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

// array for returning an unsat core.
static CVC_Exp *inconsistent_exps = NULL;

extern "C" void CVC_Inconsistent(CVC_VC vc, long *psize, CVC_Exp **pexps)
{
  GetVC;
  try {
    std::vector<CVC3::Expr> assertions;
    bool ret = cvc->inconsistent(assertions);
    Assert(ret);

    // make sure we have room to store the unsat core.
    unsigned needed = sizeof(CVC_Exp) * assertions.size();
    inconsistent_exps = (CVC_Exp*) realloc(inconsistent_exps, needed);

    for (unsigned i = 0; i < assertions.size(); ++i)
      inconsistent_exps[i] = ToExp(assertions[i]);

    *psize = assertions.size();
    *pexps = inconsistent_exps;
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Type CVC_TypeBool(CVC_VC vc)
{
  GetVC;
  try {
    return ToType(cvc->boolType());
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Type CVC_TypeInt(CVC_VC vc)
{
  GetVC;
  try {
    return ToType(cvc->intType());
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Type CVC_TypeFunc(CVC_VC vc, CVC_Type ret,
                                 CVC_Type *args, int num_args)
{
  GetVC;
  try {
    std::vector<CVC3::Type> cvc_args;
    for (int i = 0; i < num_args; i++)
      cvc_args.push_back(FromType(args[i]));
    return ToType(cvc->funType(cvc_args, FromType(ret)));
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Op CVC_NewOp(CVC_VC vc, const char *name, CVC_Type type)
{
  GetVC;
  try {
    CVC3::Op op = cvc->createOp(name, FromType(type));
    return (CVC_Op)(ToExp(cvc->getEM()->newLeafExpr(op)));
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Exp CVC_ExpInt(CVC_VC vc, long value)
{
  GetVC;
  try {
    return ToExp(cvc->ratExpr(value, 1));
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Exp CVC_ExpIntStr(CVC_VC vc, const char *str)
{
  GetVC;
  try {
    return ToExp(cvc->ratExpr(str, "1", 10));
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C"
CVC_Exp CVC_ExpBool(CVC_VC vc, int value)
{
  GetVC;
  try {
    return value ? ToExp(cvc->trueExpr()) : ToExp(cvc->falseExpr());
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Exp CVC_ExpVar(CVC_VC vc, const char *name, CVC_Type type)
{
  GetVC;
  try {
    return ToExp(cvc->varExpr(name, FromType(type)));
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Exp CVC_ExpUnop(CVC_VC vc, XIL_UnopKind unop, CVC_Exp exp)
{
  GetVC;
  try {
    CVC3::Expr nexp = FromExp(exp);
    switch (unop) {
    case XIL_U_LogicalNot:  return ToExp(cvc->notExpr(nexp));
    case XIL_U_Neg:         return ToExp(cvc->uminusExpr(nexp));
    default: Assert(false);
    }
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Exp CVC_ExpBinop(CVC_VC vc, XIL_BinopKind binop,
                                CVC_Exp left_exp, CVC_Exp right_exp)
{
  GetVC;
  try {
    CVC3::Expr nleft = FromExp(left_exp);
    CVC3::Expr nright = FromExp(right_exp);
    switch (binop) {

    case XIL_B_LogicalAnd:    return ToExp(cvc->andExpr(nleft, nright));
    case XIL_B_LogicalOr:     return ToExp(cvc->orExpr(nleft, nright));

    case XIL_B_LessThan:      return ToExp(cvc->ltExpr(nleft, nright));
    case XIL_B_GreaterThan:   return ToExp(cvc->gtExpr(nleft, nright));
    case XIL_B_LessEqual:     return ToExp(cvc->leExpr(nleft, nright));
    case XIL_B_GreaterEqual:  return ToExp(cvc->geExpr(nleft, nright));
    case XIL_B_Equal:         return ToExp(cvc->eqExpr(nleft, nright));
    case XIL_B_NotEqual:
      return ToExp(cvc->notExpr(cvc->eqExpr(nleft, nright)));

    case XIL_B_Plus:   return ToExp(cvc->plusExpr(nleft, nright));
    case XIL_B_Minus:  return ToExp(cvc->minusExpr(nleft, nright));
    case XIL_B_Mult:   return ToExp(cvc->multExpr(nleft, nright));
    case XIL_B_Max:
      return ToExp(cvc->iteExpr(cvc->geExpr(nleft, nright), nleft, nright));
    case XIL_B_Min:
      return ToExp(cvc->iteExpr(cvc->leExpr(nleft, nright), nleft, nright));

    default: Assert(false);
    }
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Exp CVC_ExpITE(CVC_VC vc,
                              CVC_Exp _if, CVC_Exp _then, CVC_Exp _else)
{
  GetVC;
  try {
    return ToExp(cvc->iteExpr(FromExp(_if), FromExp(_then), FromExp(_else)));
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" CVC_Exp CVC_ExpApply(CVC_VC vc, CVC_Op op,
                                CVC_Exp *args, int num_args)
{
  GetVC;
  try {
    CVC3::Op nop(FromExp(op).getOp());
    std::vector<CVC3::Expr> cvc_args;
    for (int i = 0; i < num_args; i++)
      cvc_args.push_back(FromExp(args[i]));
    return ToExp(cvc->funExpr(nop, cvc_args));
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" void CVC_ExpPrint(CVC_VC vc, CVC_Exp exp)
{
  GetVC;
  try {
    cvc->printExpr(FromExp(exp));
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" const char* CVC_ExpToString(CVC_Exp exp)
{
  try {
    static std::string tmp;
    tmp = FromExp(exp).toString();
    return tmp.c_str();
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}

extern "C" bool CVC_ExpIsInteger(CVC_Exp exp)
{
  try {
    // only constant integers should be floating around.
    return FromExp(exp).isRational();
  } catch (CVC3::Exception ex) {
    ExceptionFail(ex);
  }
}
