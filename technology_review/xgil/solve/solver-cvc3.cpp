
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

#include "solver-cvc3.h"

#ifndef SOLVER_CVC3
#error "solver-cvc3.cpp requires SOLVER_CVC3"
#endif

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// SolverCVC3
/////////////////////////////////////////////////////////////////////

SolverCVC3::SolverCVC3(Solver *parent, bool trace)
  : BaseSolver(parent), m_trace(trace), m_vc(NULL), m_var_count(0)
{
  // all other initialization is done in Clear().
  Clear();
}

void SolverCVC3::Clear()
{
  if (m_vc) {
    CVC_DeleteVC(m_vc);
    m_vc = NULL;
  }

  if (m_trace)
    logout << "CLEAR;" << endl;

  m_decl_names.Clear();
}

void SolverCVC3::PushContext()
{
  GetVC();
  CVC_Push(m_vc);

  if (m_trace)
    logout << "PUSH;" << endl;

  m_decl_names.PushContext();
}

void SolverCVC3::PopContext()
{
  GetVC();
  CVC_Pop(m_vc);

  if (m_trace)
    logout << "POP;" << endl;

  m_decl_names.PopContext();
}

SlvExpr SolverCVC3::MakeIntegralConstantMpz(const mpz_t value)
{
  GetVC();

  static Buffer scratch_buf;
  scratch_buf.Reset();

  IntToString(&scratch_buf, value);
  return CVC_ExpIntStr(m_vc, (const char*) scratch_buf.base);
}

SlvExpr SolverCVC3::MakeIntegralConstant(long value)
{
  GetVC();
  return CVC_ExpInt(m_vc, value);
}

SlvExpr SolverCVC3::MakeBooleanConstant(bool value)
{
  GetVC();
  return CVC_ExpBool(m_vc, value);
}

SlvDecl SolverCVC3::MakeDeclaration(FrameId frame, Exp *exp)
{
  GetVC();

  static Buffer scratch_buf;
  scratch_buf.Reset();

  BufferOutStream out(&scratch_buf);
  out << "v" << ++m_var_count << " #" << frame << " " << exp << '\0';

  char *pos = (char*) scratch_buf.base;
  while  (*pos) {
    bool ok = false;
    if (*pos >= 'a' && *pos <= 'z')
      ok = true;
    else if (*pos >= 'A' && *pos <= 'Z')
      ok = true;
    else if (*pos >= '0' && *pos <= '9')
      ok = true;

    if (!ok)
      *pos = '_';
    pos++;
  }

  char *name = (char*) scratch_buf.base;
  String *name_key = String::Make(name);

  if (m_trace)
    logout << name << " : INT;" << endl;

  CVC_Exp res = CVC_ExpVar(m_vc, name, m_int_type);

  FrameExp *pinfo = m_decl_names.Lookup(0, name_key, true);
  Assert(pinfo->exp == NULL);

  // don't need to keep a reference on the exp in the FrameExp
  // as it will also be a key in m_decl_table.
  pinfo->frame = frame;
  pinfo->exp = exp;

  return res;
}

SlvExpr SolverCVC3::GetDeclarationExpr(SlvDecl decl)
{
  GetVC();

  // CVC3 does not distinguish between variable decls and exprs.
  return decl;
}

SlvExpr SolverCVC3::GetUnop(UnopKind unop, SlvExpr exp)
{
  GetVC();
  return CVC_ExpUnop(m_vc, (XIL_UnopKind) unop, exp);
}

SlvExpr SolverCVC3::GetBinop(BinopKind binop,
                             SlvExpr left_exp, SlvExpr right_exp)
{
  GetVC();
  return CVC_ExpBinop(m_vc, (XIL_BinopKind) binop, left_exp, right_exp);
}

SlvExpr SolverCVC3::GetUninterpretedUnop(UnopKind unop, SlvExpr exp)
{
  GetVC();

  Assert(unop < XIL_UNOP_COUNT);
  CVC_Op func = m_unary_functions[unop];
  Assert(func);

  CVC_Exp args[] = { exp };
  return CVC_ExpApply(m_vc, func, args, 1);
}

SlvExpr SolverCVC3::GetUninterpretedBinop(BinopKind binop,
                                          SlvExpr left_exp,
                                          SlvExpr right_exp)
{
  GetVC();

  Assert(binop < XIL_BINOP_COUNT);
  CVC_Op func = m_binary_functions[binop];
  Assert(func);

  CVC_Exp args[] = { left_exp, right_exp };
  return CVC_ExpApply(m_vc, func, args, 2);
}

SlvExpr SolverCVC3::CoerceIntToBool(SlvExpr exp, bool ne_zero)
{
  GetVC();

  CVC_Exp zero_exp = CVC_ExpInt(m_vc, 0);

  if (ne_zero)
    return CVC_ExpBinop(m_vc, XIL_B_NotEqual, exp, zero_exp);
  else
    return CVC_ExpBinop(m_vc, XIL_B_Equal, exp, zero_exp);
}

SlvExpr SolverCVC3::CoerceBoolToInt(SlvExpr exp)
{
  GetVC();

  CVC_Exp zero_exp = CVC_ExpInt(m_vc, 0);
  CVC_Exp one_exp = CVC_ExpInt(m_vc, 1);

  return CVC_ExpITE(m_vc, exp, one_exp, zero_exp);
}

void SolverCVC3::BaseAssert(SlvExpr exp)
{
  GetVC();
  CVC_Assert(m_vc, exp);

  if (m_trace)
    logout << "ASSERT " << CVC_ExpToString(exp) << ";" << endl;
}

bool SolverCVC3::BaseCheck()
{
  GetVC();

  // querying the satisfiability of a context can change the formulas
  // it subsequently regards as satisfiable, so wrap the queries
  // in a push/pop to make sure the state gets restored.

  CVC_Push(m_vc);
  int res = CVC_Query(m_vc, m_false);
  CVC_Pop(m_vc);

  if (m_trace)
    logout << "PUSH; CHECKSAT TRUE; POP;" << endl;

  if (res) {
    // implied by the asserted exprs, thus the system
    // is unsatisfiable (false implies false).
    //if (m_trace)
    //  logout << "Unsatisfiable." << endl;
    return false;
  }
  else {
    // not implied by the asserted exprs, thus the system
    // is satisfiable.
    //if (m_trace)
    //  logout << "Satisfiable." << endl;
    return true;
  }
}

void SolverCVC3::GetAssignment(SolverDeclTable &decl_table,
                               SolverAssignment &assign)
{
  Assert(m_vc);
  Assert(assign.IsEmpty());

  // get the assignment. because of the push/pop in BaseCheck,
  // the assignment is no longer around when we get here so we have
  // to redo the SAT query.
  CVC_Push(m_vc);

  int res = CVC_Query(m_vc, m_false);
  Assert(res == 0);

  long size = 0;
  CVC_Exp *vars = NULL, *vals = NULL;

  CVC_GetConcreteModel(m_vc, &size, &vars, &vals);
  Assert(size >= 0);

  for (size_t ind = 0; ind < (size_t) size; ind++) {
    CVC_Exp var = vars[ind];
    CVC_Exp val = vals[ind];

    const char *var_str = CVC_ExpToString(var);
    String *var_key = String::Make(var_str);

    FrameExp *pinfo = m_decl_names.Lookup(0, var_key, false);

    if (!pinfo)
      continue;

    const char *val_str = CVC_ExpModelInteger(val);

    if (!val_str) {
      logout << "ERROR: Could not extract value from assignment: "
             << CVC_ExpToString(val) << endl;
      continue;
    }

    Vector<mpz_value> *values = assign.Lookup(*pinfo, true);
    Assert(values->Empty());

    values->PushBack(mpz_value());
    mpz_init(values->At(0).n);

    Try(StringToInt(val_str, values->At(0).n));
  }

  CVC_Pop(m_vc);
}

void SolverCVC3::PrintUnsatCore()
{
  GetVC();

  long size = 0;
  CVC_Exp *asserts = NULL;

  CVC_Inconsistent(m_vc, &size, &asserts);
  Assert(size >= 0);

  logout << "UNSAT Core:" << endl;
  for (size_t ind = 0; ind < (size_t) size; ind++)
    PrintRawData(asserts[ind], true);

  abort();
}

void SolverCVC3::PrintRawData(SlvExpr exp, bool is_boolean)
{
  CVC_ExpPrint(m_vc, exp);
}

void SolverCVC3::DebugPrintDecl(SlvDecl decl, bool is_boolean)
{
  const char *data = CVC_ExpToString(decl);
  logout << data << " : " << (is_boolean ? "BOOL" : "INT") << ";" << endl;
}

void SolverCVC3::DebugPrintAssign(SlvDecl decl, const mpz_t value)
{
  const char *data = CVC_ExpToString(decl);
  logout << "ASSERT " << data << " = " << value << ";" << endl;
}

void SolverCVC3::DebugPrintAssert(SlvExpr exp)
{
  const char *data = CVC_ExpToString(exp);
  logout << "ASSERT " << data << ";" << endl;
}

void SolverCVC3::GetVC()
{
  if (m_vc)
    return;

  m_vc = CVC_NewVC();

  // get a false expression for queries.
  m_false = CVC_ExpBool(m_vc, false);

  // get the builtin types for ints and bools.
  m_int_type = CVC_TypeInt(m_vc);
  m_bool_type = CVC_TypeBool(m_vc);

  CVC_Type unary_args[] = { m_int_type };
  CVC_Type unary_type = CVC_TypeFunc(m_vc, m_int_type, unary_args, 1);

  CVC_Type binary_args[] = { m_int_type, m_int_type };
  CVC_Type binary_type = CVC_TypeFunc(m_vc, m_int_type, binary_args, 2);

  const char* unop_names[XIL_UNOP_COUNT];
  memset(unop_names, 0, sizeof(unop_names));

#define SET_UNOP_NAME(NAME, INDEX)  unop_names[INDEX] = "unop_" #NAME;
  XIL_ITERATE_UNOP(SET_UNOP_NAME)
#undef SET_UNOP_NAME

  const char* binop_names[XIL_BINOP_COUNT];
  memset(binop_names, 0, sizeof(binop_names));

#define SET_BINOP_NAME(NAME, INDEX)  binop_names[INDEX] = "binop_" #NAME;
  XIL_ITERATE_BINOP(SET_BINOP_NAME)
#undef SET_BINOP_NAME

  for (size_t ind = 0; ind < XIL_UNOP_COUNT; ind++) {
    if (unop_names[ind]) {
      m_unary_functions[ind] = CVC_NewOp(m_vc, unop_names[ind], unary_type);
      if (m_trace)
        logout << unop_names[ind] << ": (INT) -> INT;" << endl;
    }
    else {
      m_unary_functions[0] = NULL;
    }
  }

  for (size_t ind = 0; ind < XIL_BINOP_COUNT; ind++) {
    if (binop_names[ind]) {
      m_binary_functions[ind] = CVC_NewOp(m_vc, binop_names[ind], binary_type);
      if (m_trace)
        logout << binop_names[ind] << ": (INT,INT) -> INT;" << endl;
    }
    else {
      m_binary_functions[ind] = NULL;
    }
  }
}

NAMESPACE_XGILL_END
