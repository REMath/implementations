
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

// Bit solver interface for the CVC3 SMT solver.

#ifndef SOLVER_CVC3
#error "solver-cvc3.h requires SOLVER_CVC3"
#endif

#include "solver.h"
#include "cvc3_interface.h"

NAMESPACE_XGILL_BEGIN

class SolverCVC3 : public BaseSolver
{
 public:
  SolverCVC3(Solver *parent, bool trace = false);

  const char* Name() const { return "CVC3"; }

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

  void DebugPrintDecl(SlvDecl decl, bool is_boolean);
  void DebugPrintAssign(SlvDecl decl, const mpz_t value);
  void DebugPrintAssert(SlvExpr expr);

 private:

  // fills in m_vc with a new VC and does other setup, if necessary.
  // clears out a model if there is one.
  void GetVC();

 private:

  // print output suitable for passing to CVC3 at the command line.
  bool m_trace;

  // validity checking context for CVC3.
  CVC_VC m_vc;

  // false expression, used for checking satisfiability of the asserts.
  CVC_Exp m_false;

  // inverse of m_decl_table, mapping names of CVC3 variables to
  // the expressions/frames used to construct those variables.
  SolverHashTable<String,FrameExp> m_decl_names;

  // number of variables we have generated for this VC, including ones that
  // have gone out of scope due to a context pop.
  size_t m_var_count;

  // type of integral values.
  CVC_Type m_int_type;

  // type of boolean values.
  CVC_Type m_bool_type;

  // uninterpreted function symbols for the unops. these are int -> int.
  CVC_Op m_unary_functions[XIL_UNOP_COUNT];

  // uninterpreted function symbols for the binops. these are int x int -> int.
  CVC_Op m_binary_functions[XIL_BINOP_COUNT];
};

NAMESPACE_XGILL_END
