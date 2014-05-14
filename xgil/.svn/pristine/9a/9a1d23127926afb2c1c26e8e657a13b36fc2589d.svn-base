
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

#include "solver-yices.h"

#ifndef SOLVER_YICES
#error "solver-yices.cpp requires SOLVER_YICES"
#endif

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// SolverYices
/////////////////////////////////////////////////////////////////////

SolverYices::SolverYices(Solver *parent)
  : BaseSolver(parent), m_context(NULL)
{
#ifdef DEBUG
  static bool enabled_typecheck = false;
  if (!enabled_typecheck) {
    yices_enable_type_checker(1);
    enabled_typecheck = true;
  }
#endif

  // all other initialization is done in Clear().
  Clear();
}

void SolverYices::Clear()
{
  if (m_context) {
    wrap_yices_del_context(m_context);
    m_context = NULL;
  }

#ifdef DEBUG
  for (size_t ind = 0; ind < m_asserted_exprs.Size(); ind++) {
    if (m_asserted_exprs[ind])
      delete m_asserted_exprs[ind];
  }
  m_asserted_exprs.Clear();
  m_asserted_exprs.PushBack(NULL);
#endif // DEBUG
}

void SolverYices::PushContext()
{
  GetContext();
  wrap_yices_push(m_context);

#ifdef DEBUG
  m_asserted_exprs.PushBack(NULL);
#endif // DEBUG
}

void SolverYices::PopContext()
{
  GetContext();
  wrap_yices_pop(m_context);

#ifdef DEBUG
  if (m_asserted_exprs.Back())
    delete m_asserted_exprs.Back();
  m_asserted_exprs.PopBack();
#endif // DEBUG
}

SlvExpr SolverYices::MakeIntegralConstantMpz(const mpz_t value)
{
  GetContext();
  return wrap_yices_mk_num_from_mpz(m_context, value);
}

SlvExpr SolverYices::MakeIntegralConstant(long value)
{
  GetContext();
  return wrap_yices_mk_num(m_context, value);
}

SlvExpr SolverYices::MakeBooleanConstant(bool value)
{
  GetContext();

  if (value)
    return wrap_yices_mk_true(m_context);
  else
    return wrap_yices_mk_false(m_context);
}

SlvDecl SolverYices::MakeDeclaration(FrameId frame, Exp *exp)
{
  GetContext();

  static Buffer scratch_buf;
  scratch_buf.Reset();

  BufferOutStream out(&scratch_buf);
  out << "#" << frame << " " << exp
      << " [" << (void*) exp << "]" << '\0';
  char *name = (char*) scratch_buf.base;

  return wrap_yices_mk_var_decl(m_context, name, m_int_type);
}

SlvExpr SolverYices::GetDeclarationExpr(SlvDecl decl)
{
  GetContext();
  return wrap_yices_mk_var_from_decl(m_context, (yices_var_decl) decl);
}

SlvExpr SolverYices::GetUnop(UnopKind unop, SlvExpr value)
{
  GetContext();

  yices_expr exp = (yices_expr) value;

  switch (unop) {

  // operations with boolean operand and result.
  case U_LogicalNot:
    return wrap_yices_mk_not(m_context, exp);

  // operations with integral operand and result.
  case U_Neg: {
    yices_expr zero_expr = wrap_yices_mk_num(m_context, 0);
    yices_expr args[2] = { zero_expr, exp };
    return wrap_yices_mk_sub(m_context, args, 2);
  }

  default:
    Assert(false);
  }
}

SlvExpr SolverYices::GetBinop(BinopKind binop,
                              SlvExpr left_value, SlvExpr right_value)
{
  GetContext();

  yices_expr left_exp = (yices_expr) left_value;
  yices_expr right_exp = (yices_expr) right_value;

  switch (binop) {

  // operations with boolean operands and result.
  case B_LogicalAnd: {
    yices_expr args[2] = { left_exp, right_exp };
    return wrap_yices_mk_and(m_context, args, 2);
  }
  case B_LogicalOr: {
    yices_expr args[2] = { left_exp, right_exp };
    return wrap_yices_mk_or(m_context, args, 2);
  }

  // operations with integral operands and boolean result.
  case B_LessThan:
    return wrap_yices_mk_lt(m_context, left_exp, right_exp);
  case B_GreaterThan:
    return wrap_yices_mk_gt(m_context, left_exp, right_exp);
  case B_LessEqual:
    return wrap_yices_mk_le(m_context, left_exp, right_exp);
  case B_GreaterEqual:
    return wrap_yices_mk_ge(m_context, left_exp, right_exp);
  case B_Equal:
    return wrap_yices_mk_eq(m_context, left_exp, right_exp);
  case B_NotEqual:
    return wrap_yices_mk_diseq(m_context, left_exp, right_exp);

  // operations with integral operands and result.
  case B_Plus: {
    yices_expr args[2] = { left_exp, right_exp };
    return wrap_yices_mk_sum(m_context, args, 2);
  }
  case B_Minus: {
    yices_expr args[2] = { left_exp, right_exp };
    return wrap_yices_mk_sub(m_context, args, 2);
  }
  case B_Mult: {
    yices_expr args[2] = { left_exp, right_exp };
    return wrap_yices_mk_mul(m_context, args, 2);
  }
  case B_Max: {
    yices_expr ge_exp = wrap_yices_mk_ge(m_context, left_exp, right_exp);
    return wrap_yices_mk_ite(m_context, ge_exp, left_exp, right_exp);
  }
  case B_Min: {
    yices_expr le_exp = wrap_yices_mk_le(m_context, left_exp, right_exp);
    return wrap_yices_mk_ite(m_context, le_exp, left_exp, right_exp);
  }

  default:
    Assert(false);
  }
}

SlvExpr SolverYices::GetUninterpretedUnop(UnopKind unop, SlvExpr value)
{
  GetContext();

  Assert(unop < XIL_UNOP_COUNT);
  yices_expr func = m_unary_functions[unop];
  Assert(func);

  yices_expr app_args[1] = { (yices_expr) value };
  yices_expr res = wrap_yices_mk_app(m_context, func, app_args, 1);

  return res;
}

SlvExpr SolverYices::GetUninterpretedBinop(BinopKind binop,
                                           SlvExpr left_value,
                                           SlvExpr right_value)
{
  GetContext();

  Assert(binop < XIL_BINOP_COUNT);
  yices_expr func = m_binary_functions[binop];
  Assert(func);

  yices_expr app_args[2] = { (yices_expr) left_value,
                             (yices_expr) right_value };
  yices_expr res = wrap_yices_mk_app(m_context, func, app_args, 2);

  return res;
}

SlvExpr SolverYices::CoerceIntToBool(SlvExpr value, bool ne_zero)
{
  GetContext();

  yices_expr zero_expr = wrap_yices_mk_num(m_context, 0);
  if (ne_zero)
    return wrap_yices_mk_diseq(m_context, (yices_expr) value, zero_expr);
  else
    return wrap_yices_mk_eq(m_context, (yices_expr) value, zero_expr);
}

SlvExpr SolverYices::CoerceBoolToInt(SlvExpr value)
{
  GetContext();

  yices_expr zero_expr = yices_mk_num(m_context, 0);
  yices_expr one_expr = yices_mk_num(m_context, 1);

  return wrap_yices_mk_ite(m_context, (yices_expr) value, one_expr, zero_expr);
}

void SolverYices::BaseAssert(SlvExpr exp)
{
  GetContext();

  // use retractable asserts in DEBUG mode. see PrintUnsatCore().
#ifdef DEBUG

  SlvRetract retract;
  retract.expr = exp;
  retract.id = wrap_yices_assert_retractable(m_context, exp);

  Vector<SlvRetract> *&asserts = m_asserted_exprs.Back();
  if (asserts == NULL)
    asserts = new Vector<SlvRetract>();
  asserts->PushBack(retract);

#else // DEBUG

  wrap_yices_assert(m_context, exp);

#endif // DEBUG

}

bool SolverYices::BaseCheck()
{
  GetContext();

  lbool res = wrap_yices_check(m_context);
  Assert(res != l_undef);

  return (res == l_true);
}

void SolverYices::GetAssignment(SolverDeclTable &decl_table,
                                SolverAssignment &assign)
{
  Assert(m_context);

  // yices wants the context checked before getting the assign.
  lbool result = wrap_yices_check(m_context);
  Assert(result == l_true);

  yices_model model = wrap_yices_get_model(m_context);
  Assert(model);

  HashIterate(decl_table) {
    FrameId frame = decl_table.ItFrame();
    Exp *exp = decl_table.ItKey();
    SlvDecl decl = decl_table.ItValue();

    if (Solver::IsBoolean(exp)) {
      lbool val = wrap_yices_get_value(model, decl);

      if (val != l_undef) {
        Vector<mpz_value> *values = assign.Lookup(FrameExp(frame, exp), true);
        Assert(values->Empty());

        values->PushBack(mpz_value());
        mpz_init(values->At(0).n);

        mpz_set_si(values->At(0).n, (val == l_true) ? 1 : 0);
      }
    }
    else {
      mpz_t res;
      mpz_init(res);

      int ret = wrap_yices_get_mpz_value(model, (yices_var_decl) decl, res);

      if (ret == 0) {
        mpz_clear(res);
      }
      else {
        Vector<mpz_value> *values = assign.Lookup(FrameExp(frame, exp), true);
        Assert(values->Empty());

        values->PushBack(mpz_value());
        mpz_init(values->At(0).n);

        mpz_set(values->At(0).n, res);
        mpz_clear(res);
      }
    }
  }
}

void SolverYices::PrintUnsatCore()
{
  // we can only generate unsat cores for retractable asserts,
  // which we use in DEBUG mode (retractable asserts may be a good deal
  // slower than regular asserts).
#ifdef DEBUG

  // TODO: newer versions of Yices support this directly in the API.

  // algorithm: go through the list of everything we have asserted,
  // and retract any assert such that removing that assert preserves
  // the unsatisfiability of the system. the assertions left at the
  // end are the core that we print out.

  // make a list of all the retractable asserts we have.
  // these are references because we will need to update
  // the assertion IDs as we retract and then reassert exprs.
  Vector<SlvRetract> all_asserts;

  for (size_t ind = 0; ind < m_asserted_exprs.Size(); ind++) {
    Vector<SlvRetract> *cxt_asserts = m_asserted_exprs[ind];
    if (cxt_asserts) {
      for (size_t cind = 0; cind < cxt_asserts->Size(); cind++)
        all_asserts.PushBack(cxt_asserts->At(cind));
    }
  }

  logout << "UNSAT Core:" << endl;

  for (size_t ind = 0; ind < all_asserts.Size(); ind++) {
    yices_expr expr = all_asserts[ind].expr;
    assertion_id id = all_asserts[ind].id;

    wrap_yices_retract(m_context, id);

    bool result = BaseCheck();
    if (result) {
      // now the system is satisfiable. the assertion is part of the core
      // so print it out and reassert it.

      PrintRawData(expr, true);
      logout << endl;

      wrap_yices_assert(m_context, expr);

      result = BaseCheck();
      Assert(!result);
    }
    else {
      // system is still unsatisfiable. leave the assertion out of the core
      // and do not reassert it.
    }
  }

#else // DEBUG

  logout << "ERROR: Can't generate unsat cores in release mode" << endl;

#endif // DEBUG

  logout << flush;

  // abort analysis.
  abort();
}

void SolverYices::PrintRawData(SlvExpr value, bool is_boolean)
{
  wrap_yices_pp_expr((yices_expr) value);
}

void SolverYices::GetContext()
{
  if (m_context)
    return;

  m_context = wrap_yices_mk_context();

  // get the yices builtin types for ints and bools.
  m_int_type = wrap_yices_mk_type(m_context, "int");
  m_bool_type = wrap_yices_mk_type(m_context, "bool");

  yices_type unary_args[1] = { m_int_type };
  yices_expr unary_function_type =
    wrap_yices_mk_function_type(m_context, unary_args, 1, m_int_type);

  yices_type binary_args[2] = { m_int_type, m_int_type };
  yices_expr binary_function_type =
    wrap_yices_mk_function_type(m_context, binary_args, 2, m_int_type);

  char scratch[100];

  for (size_t ind = 0; ind < XIL_UNOP_COUNT; ind++) {
    const char *unop_str = UnopString((UnopKind) ind);
    if (unop_str) {
      sprintf(scratch, "unop.%s", unop_str);

      yices_var_decl decl =
        wrap_yices_mk_var_decl(m_context, scratch, unary_function_type);
      yices_expr func = wrap_yices_mk_var_from_decl(m_context, decl);
      m_unary_functions[ind] = func;
    }
    else {
      m_unary_functions[0] = NULL;
    }
  }

  for (size_t ind = 0; ind < XIL_BINOP_COUNT; ind++) {
    const char *binop_str = BinopString((BinopKind) ind);
    if (binop_str) {
      sprintf(scratch, "binop.%s", binop_str);

      yices_var_decl decl =
        wrap_yices_mk_var_decl(m_context, scratch, binary_function_type);
      yices_expr func = wrap_yices_mk_var_from_decl(m_context, decl);
      m_binary_functions[ind] = func;
    }
    else {
      m_binary_functions[ind] = NULL;
    }
  }
}

NAMESPACE_XGILL_END
