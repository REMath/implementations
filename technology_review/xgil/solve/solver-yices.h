
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

#pragma once

// Bit solver interface for the Yices SMT solver.

#ifndef SOLVER_YICES
#error "solver-yices.h requires SOLVER_YICES"
#endif

#include "solver.h"
#include "wrapyices.h"

NAMESPACE_XGILL_BEGIN

class SolverYices : public BaseSolver
{
 public:
  SolverYices(Solver *parent);

  const char* Name() const { return "Yices"; }

  void Clear();
  void PushContext();
  void PopContext();

  SlvExpr MakeIntegralConstantMpz(const mpz_t value);
  SlvExpr MakeIntegralConstant(long value);
  SlvExpr MakeBooleanConstant(bool value);
  SlvDecl MakeDeclaration(FrameId frame, Exp *exp);
  SlvExpr GetDeclarationExpr(SlvDecl decl);
  SlvExpr GetUnop(UnopKind unop, SlvExpr exp);
  SlvExpr GetBinop(BinopKind binop,
                   SlvExpr left_exp, SlvExpr right_exp);
  SlvExpr GetUninterpretedUnop(UnopKind unop, SlvExpr exp);
  SlvExpr GetUninterpretedBinop(BinopKind binop,
                                SlvExpr left_exp, SlvExpr right_exp);
  SlvExpr CoerceIntToBool(SlvExpr exp, bool ne_zero);
  SlvExpr CoerceBoolToInt(SlvExpr exp);

  void BaseAssert(SlvExpr exp);
  bool BaseCheck();
  void GetAssignment(SolverDeclTable &decl_table,
                     SolverAssignment &assign);

  void PrintUnsatCore();
  void PrintRawData(SlvExpr exp, bool is_boolean);

 private:

  // fills in m_context with a new context and does other setup, if necessary.
  void GetContext();

  // solving context for Yices.
  yices_context m_context;

  // type of integral values.
  yices_type m_int_type;

  // type of boolean values.
  yices_type m_bool_type;

  // uninterpreted function symbols for the unops. these are int -> int.
  yices_expr m_unary_functions[XIL_UNOP_COUNT];

  // uninterpreted function symbols for the binops. these are int x int -> int.
  yices_expr m_binary_functions[XIL_BINOP_COUNT];

  // data on a retractable assertion. if all assertions are retractable we
  // can extract pseudo-unsat cores from the system (for debugging).
  struct SlvRetract {
    yices_expr expr;  // asserted expression.
    assertion_id id;  // id for retracting assert.
    SlvRetract() : expr(NULL), id(0) {}
  };

  // expressions that have been retractably asserted in each context.
  // used only for debugging if we need an unsat core.
  Vector<Vector<SlvRetract>*> m_asserted_exprs;
};

NAMESPACE_XGILL_END
