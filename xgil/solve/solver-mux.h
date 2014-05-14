
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

// solver interface for cross-checking and comparing performance for
// multiple solver backends.

#include "solver.h"

NAMESPACE_XGILL_BEGIN

class SolverMUX : public BaseSolver
{
 public:
  // make a MUX solver for the specified backends. takes ownership
  // of each backend in the list.
  SolverMUX(Solver *parent, const Vector<BaseSolver*> &solvers);
  ~SolverMUX();

  const char* Name() const { return "MUX"; }
  void PrintTimers() const;

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
  // all the backend solvers we are comparing.
  Vector<BaseSolver*> m_solvers;

  // aggregate time spent solving (assert/check/getassign) for each backend.
  Vector<uint64_t> m_elapsed;

  // all the declarations and expressions we have generated for each backend.
  // returned/passed SlvDecl/SlvExpr values for this solver are indexes here,
  // where m_decl_list[0][N], m_decl_list[1][N] and so forth represent the
  // same abstract value in the different backends.
  Vector< Vector<SlvDecl> > m_decl_list;
  Vector< Vector<SlvExpr> > m_expr_list;

  // solver to use for generating assignments or printing unsat cores.
  size_t m_assign_solver;

  // get a new index for a declaration or expression.
  size_t GetNewDecl();
  size_t GetNewExpr();
};

NAMESPACE_XGILL_END
