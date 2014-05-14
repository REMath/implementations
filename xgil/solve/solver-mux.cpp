
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

#include "solver-mux.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// SolverMUX
/////////////////////////////////////////////////////////////////////

SolverMUX::SolverMUX(Solver *parent, const Vector<BaseSolver*> &solvers)
  : BaseSolver(parent), m_assign_solver(0)
{
  Assert(!solvers.Empty());

  for (size_t ind = 0; ind < solvers.Size(); ind++) {
    m_solvers.PushBack(solvers[ind]);
    m_elapsed.PushBack(0);
    m_decl_list.PushBack(Vector<SlvDecl>());
    m_expr_list.PushBack(Vector<SlvExpr>());
  }

  // zero is not recognized as a valid SlvDecl/SlvExpr by Solver.
  GetNewDecl();
  GetNewExpr();
}

SolverMUX::~SolverMUX()
{
  for (size_t ind = 0; ind < m_solvers.Size(); ind++)
    delete m_solvers[ind];
}

void SolverMUX::PrintTimers() const
{
  logout << "Solver EACH:";
  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    logout << " " << m_solvers[ind]->Name() << ": ";
    PrintTime(m_elapsed[ind]);
  }
  logout << endl;
}

void SolverMUX::Clear()
{
  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    m_solvers[ind]->Clear();
    m_elapsed[ind] = 0;
    m_decl_list[ind].Clear();
    m_expr_list[ind].Clear();
  }

  GetNewDecl();
  GetNewExpr();
}

void SolverMUX::PushContext()
{
  for (size_t ind = 0; ind < m_solvers.Size(); ind++)
    m_solvers[ind]->PushContext();
}

void SolverMUX::PopContext()
{
  for (size_t ind = 0; ind < m_solvers.Size(); ind++)
    m_solvers[ind]->PopContext();
}

SlvExpr SolverMUX::MakeIntegralConstantMpz(const mpz_t value)
{
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvExpr exp = m_solvers[ind]->MakeIntegralConstantMpz(value);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

SlvExpr SolverMUX::MakeIntegralConstant(long value)
{
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvExpr exp = m_solvers[ind]->MakeIntegralConstant(value);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

SlvExpr SolverMUX::MakeBooleanConstant(bool value)
{
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvExpr exp = m_solvers[ind]->MakeBooleanConstant(value);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

SlvDecl SolverMUX::MakeDeclaration(FrameId frame, Exp *exp)
{
  size_t res = GetNewDecl();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvDecl decl = m_solvers[ind]->MakeDeclaration(frame, exp);
    m_decl_list[ind][res] = decl;
  }

  return (SlvDecl) res;
}

SlvExpr SolverMUX::GetDeclarationExpr(SlvDecl decl)
{
  size_t ind_decl = (size_t) decl;
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvDecl new_decl = m_decl_list[ind][ind_decl];
    SlvExpr exp = m_solvers[ind]->GetDeclarationExpr(new_decl);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

SlvExpr SolverMUX::GetUnop(UnopKind unop, SlvExpr exp)
{
  size_t ind_exp = (size_t) exp;
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvExpr new_exp = m_expr_list[ind][ind_exp];
    SlvExpr exp = m_solvers[ind]->GetUnop(unop, new_exp);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

SlvExpr SolverMUX::GetBinop(BinopKind binop,
                             SlvExpr left_exp, SlvExpr right_exp)
{
  size_t ind_left_exp = (size_t) left_exp;
  size_t ind_right_exp = (size_t) right_exp;
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvExpr new_left_exp = m_expr_list[ind][ind_left_exp];
    SlvExpr new_right_exp = m_expr_list[ind][ind_right_exp];
    SlvExpr exp = m_solvers[ind]->GetBinop(binop, new_left_exp, new_right_exp);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

SlvExpr SolverMUX::GetUninterpretedUnop(UnopKind unop, SlvExpr exp)
{
  size_t ind_exp = (size_t) exp;
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvExpr new_exp = m_expr_list[ind][ind_exp];
    SlvExpr exp = m_solvers[ind]->GetUninterpretedUnop(unop, new_exp);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

SlvExpr SolverMUX::GetUninterpretedBinop(BinopKind binop,
                                         SlvExpr left_exp,
                                         SlvExpr right_exp)
{
  size_t ind_left_exp = (size_t) left_exp;
  size_t ind_right_exp = (size_t) right_exp;
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvExpr new_left_exp = m_expr_list[ind][ind_left_exp];
    SlvExpr new_right_exp = m_expr_list[ind][ind_right_exp];
    SlvExpr exp = m_solvers[ind]->GetUninterpretedBinop(binop, new_left_exp,
                                                        new_right_exp);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

SlvExpr SolverMUX::CoerceIntToBool(SlvExpr exp, bool ne_zero)
{
  size_t ind_exp = (size_t) exp;
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvExpr new_exp = m_expr_list[ind][ind_exp];
    SlvExpr exp = m_solvers[ind]->CoerceIntToBool(new_exp, ne_zero);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

SlvExpr SolverMUX::CoerceBoolToInt(SlvExpr exp)
{
  size_t ind_exp = (size_t) exp;
  size_t res = GetNewExpr();

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    SlvExpr new_exp = m_expr_list[ind][ind_exp];
    SlvExpr exp = m_solvers[ind]->CoerceBoolToInt(new_exp);
    m_expr_list[ind][res] = exp;
  }

  return (SlvExpr) res;
}

void SolverMUX::BaseAssert(SlvExpr exp)
{
  size_t ind_exp = (size_t) exp;

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    Timer _timer(NULL);

    SlvExpr new_exp = m_expr_list[ind][ind_exp];
    m_solvers[ind]->BaseAssert(new_exp);

    m_elapsed[ind] += _timer.Elapsed();
  }
}

bool SolverMUX::BaseCheck()
{
  int true_solver = -1;
  int false_solver = -1;

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    Timer _timer(NULL);

    bool res = m_solvers[ind]->BaseCheck();

    if (res) true_solver = ind;
    else false_solver = ind;

    m_elapsed[ind] += _timer.Elapsed();
  }

  // make sure all the backends are consistent on whether the
  // constraints are satisfiable. this is the core of the
  // cross-checking we can do between the backends.
  if (true_solver >= 0 && false_solver >= 0) {
    logout << "ERROR: Conflict between solvers on satisfiability ["
           << m_parent->m_name << "]" << endl;

    // fill in the solver's satisfying assignment from the solver that
    // returned SAT.
    m_assign_solver = (size_t) true_solver;
    m_parent->PinAssign();

    // make sure this is a legitimate satisfying assignment.
    // a failure here indicates a problem with true_solver.
    m_parent->CheckAssignmentBits();

    logout << "Failed Solver: " << m_solvers[false_solver]->Name() << endl;
    abort();
  }

  return (true_solver >= 0);
}

void SolverMUX::GetAssignment(SolverDeclTable &decl_table,
                              SolverAssignment &assign)
{
  // we can only generate one assignment, so use m_assign_solver
  // (normally zero except when we found an error while cross-checking).
  // the decl table we have references SlvDecls generated by
  // *this* BaseSolver, not the backend we need, so make a new table.
  SolverDeclTable new_decl_table;

  const Vector<SlvDecl> &decl_list = m_decl_list[m_assign_solver];

  HashIterate(decl_table) {
    FrameId frame = decl_table.ItFrame();
    Exp *exp = decl_table.ItKey();
    SlvDecl decl = decl_table.ItValue();

    SlvDecl new_decl = decl_list[(size_t) decl];
    SlvDecl *pdecl = new_decl_table.Lookup(frame, exp, true);

    Assert(*pdecl == NULL);
    *pdecl = new_decl;
  }

  m_solvers[m_assign_solver]->GetAssignment(new_decl_table, assign);
}

void SolverMUX::PrintUnsatCore()
{
  m_solvers[m_assign_solver]->PrintUnsatCore();
}

void SolverMUX::PrintRawData(SlvExpr exp, bool is_boolean)
{
  size_t ind_exp = (size_t) exp;

  for (size_t ind = 0; ind < m_solvers.Size(); ind++) {
    if (ind)
      logout << " ### ";
    SlvExpr new_exp = m_expr_list[ind][ind_exp];
    m_solvers[ind]->PrintRawData(new_exp, is_boolean);
  }
}

size_t SolverMUX::GetNewDecl()
{
  size_t last = m_decl_list[0].Size();
  for (size_t ind = 0; ind < m_decl_list.Size(); ind++) {
    Assert(m_decl_list[ind].Size() == last);
    m_decl_list[ind].PushBack(NULL);
  }
  return last;
}

size_t SolverMUX::GetNewExpr()
{
  size_t last = m_expr_list[0].Size();
  for (size_t ind = 0; ind < m_expr_list.Size(); ind++) {
    Assert(m_expr_list[ind].Size() == last);
    m_expr_list[ind].PushBack(NULL);
  }
  return last;
}

NAMESPACE_XGILL_END
