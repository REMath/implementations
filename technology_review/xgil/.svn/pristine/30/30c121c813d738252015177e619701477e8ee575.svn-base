
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

#include "solver.h"
#include "solver-mux.h"

#ifdef SOLVER_YICES
#include "solver-yices.h"
#endif

#ifdef SOLVER_CVC3
#include "solver-cvc3.h"
#endif

// DEBUG
// #include <backend/transaction.h>

NAMESPACE_XGILL_BEGIN

typedef Solver::ConvertState ConvertState;

/////////////////////////////////////////////////////////////////////
// Solver static
/////////////////////////////////////////////////////////////////////

ConfigOption solver_use(CK_String, "solver", "cvc3",
    "backend solver to use (yices, cvc3, mux)");

ConfigOption solver_verbose(CK_String, "solver-verbose", "",
    "print assertions and queries for a solver [all: all solvers]");

ConfigOption solver_constraint(CK_Flag, "solver-constraint", NULL,
    "also print constraint tables with -solver-verbose");

TrackAlloc g_alloc_SolverHashTable("SolverHashTable");

// special solver used for performing static equivalence and other comparison
// checks. once this is created it never goes away (but it stays empty
// when not in use).
static Solver *g_test_solver = NULL;

static inline void GetTestSolver()
{
  if (g_test_solver == NULL)
    g_test_solver = new Solver("tester");
}

bool Solver::BitSatisfiable(Bit *bit)
{
  if (bit->IsFalse())
    return false;

  GetTestSolver();
  g_test_solver->PushContext();

  ConvertState state(0, false);
  SlvExpr expr = g_test_solver->ConvertBit(state, bit);
  g_test_solver->PushAssert(expr);

  bool satisfiable = g_test_solver->IsSatisfiable();

  g_test_solver->PopContext();

  return satisfiable;
}

bool Solver::BitValid(Bit *bit)
{
  if (bit->IsTrue())
    return true;

  GetTestSolver();
  g_test_solver->PushContext();

  ConvertState state(0, false);
  SlvExpr expr = g_test_solver->ConvertBit(state, bit);
  SlvExpr not_expr = g_test_solver->m_base->GetUnop(U_LogicalNot, expr);
  g_test_solver->PushAssert(not_expr);

  bool satisfiable = g_test_solver->IsSatisfiable();

  g_test_solver->PopContext();
  return !satisfiable;
}

bool Solver::BitImplies(Bit *bit0, Bit *bit1)
{
  GetTestSolver();
  g_test_solver->PushContext();

  ConvertState state(0, false);
  SlvExpr expr0 = g_test_solver->ConvertBit(state, bit0);
  SlvExpr expr1 = g_test_solver->ConvertBit(state, bit1);
  SlvExpr not_expr1 = g_test_solver->m_base->GetUnop(U_LogicalNot, expr1);
  g_test_solver->PushAssert(expr0);
  g_test_solver->PushAssert(not_expr1);

  bool satisfiable = g_test_solver->IsSatisfiable();

  g_test_solver->PopContext();
  return !satisfiable;
}

bool Solver::BitEquivalent(Bit *bit0, Bit *bit1)
{
  GetTestSolver();
  g_test_solver->PushContext();

  ConvertState state(0, false);
  SlvExpr expr0 = g_test_solver->ConvertBit(state, bit0);
  SlvExpr expr1 = g_test_solver->ConvertBit(state, bit1);

  SlvExpr nexpr0 = g_test_solver->m_base->CoerceBoolToInt(expr0);
  SlvExpr nexpr1 = g_test_solver->m_base->CoerceBoolToInt(expr1);
  SlvExpr ne_expr = g_test_solver->m_base->GetBinop(B_NotEqual, nexpr0, nexpr1);
  g_test_solver->PushAssert(ne_expr);

  bool satisfiable = g_test_solver->IsSatisfiable();

  g_test_solver->PopContext();
  return !satisfiable;
}

// visitor to get side conditions for terms mentioned in a bit.
// TODO: we should not be following disjunction operations in the bit.
class SideConditionVisitor : public ExpVisitor
{
 public:
  // any side conditions to assert.
  Vector<Bit*> side_list;

  SideConditionVisitor()
    : ExpVisitor(VISK_All)
  {}

  // add side conditions that the specified lvalue is not a NULL dereference.
  void CheckNull(Exp *target)
  {
    while (ExpFld *ntarget = target->IfFld())
      target = ntarget->GetTarget();

    // ignore completely if the target is a constant integer (i.e. NULL).
    if (target->IsInt()) {
      Bit *false_bit = Bit::MakeConstant(false);
      side_list.PushBack(false_bit);
    }

    // otherwise add a non-NULL assumption.
    if (target->IsDrf() || target->IsClobber()) {
      Bit *nonzero_target = Exp::MakeNonZeroBit(target);
      side_list.PushBack(nonzero_target);
    }
  }

  void Visit(Exp *exp)
  {
    // expression whose value must not be NULL.
    Exp *target = NULL;

    // bounds and terminators must be on a non-NULL value.
    GetExpBoundTerminate(exp, &target, NULL, NULL);

    if (target)
      CheckNull(target);

    // access value of a pointer.
    if (exp->IsDrf() || exp->IsClobber())
      CheckNull(exp->GetLvalTarget());

    // make sure we visit overwritten values too.
    if (ExpClobber *nexp = exp->IfClobber())
      nexp->GetOverwrite()->DoVisit(this);
  }
};

void Solver::CheckDisjointBits(Bit *guard,
                               const Vector<Bit*> &bit_list)
{
  GetTestSolver();

  g_test_solver->PushContext();

  if (guard) {
    g_test_solver->AddAssert(0, guard);

    if (!g_test_solver->IsSatisfiable()) {
      g_test_solver->PopContext();
      return;
    }
  }

  // check the guard implies the disjunction of the individual bits.

  Vector<Bit*> op_list;
  for (size_t ind = 0; ind < bit_list.Size(); ind++) {
    Bit *bit = bit_list[ind];
    op_list.PushBack(bit);
  }

  SortBitList(&op_list);
  Bit *disjunct = Bit::MakeOr(op_list);
  Bit *not_disjunct = Bit::MakeNot(disjunct);

  g_test_solver->PushContext();
  g_test_solver->AddAssert(0, not_disjunct);

  if (g_test_solver->IsSatisfiable()) {
    logout << "ERROR: CheckDisjointBits disjunction failed:" << endl;
    logout << "  guard: " << guard << endl;
    for (size_t ind = 0; ind < bit_list.Size(); ind++)
      logout << "  bit: " << bit_list[ind] << endl;
    g_test_solver->PrintRawAssignment();
    logout << flush;

    Breakpoint();
  }

  g_test_solver->PopContext();

  // check the individual bits are pairwise disjoint, excluding cases
  // where the guard itself does not hold.

  for (size_t find = 0; find < bit_list.Size(); find++) {
    for (size_t sind = find + 1; sind < bit_list.Size(); sind++) {
      Bit *fop = bit_list[find];
      Bit *sop = bit_list[sind];

      g_test_solver->PushContext();

      g_test_solver->AddAssert(0, fop);
      g_test_solver->AddAssert(0, sop);

      if (g_test_solver->IsSatisfiable()) {
        logout << "ERROR: CheckDisjointBits disjoint failed:" << endl;
        logout << "  guard: " << guard << endl;
        logout << "  bit: " << fop << endl;
        logout << "  bit: " << sop << endl;
        g_test_solver->PrintRawAssignment();
        logout << flush;

        Breakpoint();
      }

      g_test_solver->PopContext();
    }
  }

  g_test_solver->PopContext();
}

static void (*old_callback_ExpSimplify)(Exp*, Exp*) = NULL;
static void (*old_callback_CvtSimplify)(Exp*, Bit*) = NULL;
static void (*old_callback_BitSimplify)(Bit*, Bit*) = NULL;

// save/restore the simplification callbacks to avoid infinite recursion
// when getting the SlvExprs for tested expressions. currently ConvertExp
// can create new temporary expressions as it runs. TODO: fix?

static void SaveSimplifyCallbacks()
{
  Assert(old_callback_ExpSimplify == NULL);
  Assert(old_callback_CvtSimplify == NULL);
  Assert(old_callback_BitSimplify == NULL);

  old_callback_ExpSimplify = g_callback_ExpSimplify;
  old_callback_CvtSimplify = g_callback_CvtSimplify;
  old_callback_BitSimplify = g_callback_BitSimplify;

  g_callback_ExpSimplify = NULL;
  g_callback_CvtSimplify = NULL;
  g_callback_BitSimplify = NULL;
}

static void RestoreSimplifyCallbacks()
{
  g_callback_ExpSimplify = old_callback_ExpSimplify;
  g_callback_CvtSimplify = old_callback_CvtSimplify;
  g_callback_BitSimplify = old_callback_BitSimplify;

  old_callback_ExpSimplify = NULL;
  old_callback_CvtSimplify = NULL;
  old_callback_BitSimplify = NULL;
}

void Solver::CheckEquivalentExp(Exp *exp0, Exp *exp1)
{
  if (exp0 == exp1)
    return;

  GetTestSolver();
  SaveSimplifyCallbacks();

  g_test_solver->PushContext();

  ConvertState state(0, false);
  SlvExpr expr0 = g_test_solver->ConvertExpIntegral(state, exp0);
  SlvExpr expr1 = g_test_solver->ConvertExpIntegral(state, exp1);

  SlvExpr ne_expr = g_test_solver->m_base->GetBinop(B_NotEqual, expr0, expr1);
  g_test_solver->PushAssert(ne_expr);

  if (g_test_solver->IsSatisfiable()) {
    logout << "ERROR: CheckEquivalentExp failed: "
           << exp0 << " " << exp1 << endl;
    g_test_solver->PrintRawAssignment();
    logout << flush;
    Breakpoint();
  }

  g_test_solver->PopContext();
  RestoreSimplifyCallbacks();
}

void Solver::CheckEquivalentCvt(Exp *exp, Bit *bit)
{
  if (bit->GetVar() == exp)
    return;

  GetTestSolver();
  SaveSimplifyCallbacks();

  g_test_solver->PushContext();

  ConvertState state(0, false);
  SlvExpr expr = g_test_solver->ConvertExpIntegral(state, exp);
  SlvExpr nez_expr = g_test_solver->m_base->CoerceIntToBool(expr, true);
  SlvExpr bit_expr = g_test_solver->ConvertBit(state, bit);

  SlvExpr nnez_expr = g_test_solver->m_base->CoerceBoolToInt(nez_expr);
  SlvExpr nbit_expr = g_test_solver->m_base->CoerceBoolToInt(bit_expr);
  SlvExpr ne_expr = g_test_solver->m_base->GetBinop(B_NotEqual, nnez_expr, nbit_expr);
  g_test_solver->PushAssert(ne_expr);

  if (g_test_solver->IsSatisfiable()) {
    logout << "ERROR: CheckEquivalentCvt failed: "
           << exp << " " << bit << endl;
    g_test_solver->PrintRawAssignment();
    logout << flush;
    Breakpoint();
  }

  g_test_solver->PopContext();
  RestoreSimplifyCallbacks();
}

void Solver::CheckEquivalentBit(Bit *bit0, Bit *bit1)
{
  if (bit0 == bit1)
    return;

  GetTestSolver();
  SaveSimplifyCallbacks();

  g_test_solver->PushContext();

  ConvertState state(0, false);
  SlvExpr expr0 = g_test_solver->ConvertBit(state, bit0);
  SlvExpr expr1 = g_test_solver->ConvertBit(state, bit1);

  SlvExpr nexpr0 = g_test_solver->m_base->CoerceBoolToInt(expr0);
  SlvExpr nexpr1 = g_test_solver->m_base->CoerceBoolToInt(expr1);
  SlvExpr ne_expr = g_test_solver->m_base->GetBinop(B_NotEqual, nexpr0, nexpr1);
  g_test_solver->PushAssert(ne_expr);

  if (g_test_solver->IsSatisfiable()) {
    logout << "ERROR: CheckEquivalentBit failed: "
           << bit0 << " " << bit1 << endl;
    g_test_solver->PrintRawAssignment();
    logout << flush;
    Breakpoint();
  }

  g_test_solver->PopContext();
  RestoreSimplifyCallbacks();
}

void Solver::CheckSimplifications()
{
  g_callback_ExpSimplify = CheckEquivalentExp;
  g_callback_CvtSimplify = CheckEquivalentCvt;
  g_callback_BitSimplify = CheckEquivalentBit;
}

bool Solver::Solver::IsBoolean(Exp *exp)
{
  // logical and comparison binops have boolean result.
  if (ExpBinop *nexp = exp->IfBinop()) {
    BinopKind binop = nexp->GetBinopKind();
    return IsLogicalBinop(binop) || IsCompareBinop(binop);
  }

  // logical negation has boolean result.
  if (ExpUnop *nexp = exp->IfUnop()) {
    if (nexp->GetUnopKind() == U_LogicalNot)
      return true;
    return false;
  }

  // other expressions are integral.
  return false;
}

static bool IsTermExp(Exp *exp)
{
  return exp->IsLvalue() || exp->IsInitial()
      || exp->IsExit() || exp->IsNullTest();
}

bool IsNonNegative(Exp *exp)
{
  // all expressions are treated as nonnegative except those explicitly
  // declared with a signed integer type.
  Exp *target = NULL;

  switch (exp->Kind()) {
  case EK_Drf:
  case EK_Clobber:
  case EK_Initial:
    target = exp->GetLvalTarget();
    break;
  case EK_Val:
    if (exp->AsVal()->GetValueKind() == NULL)
      target = exp->AsVal()->GetLvalue();
    break;
  default:
    break;
  }

  if (target) {
    Type *type = target->GetType();
    if (type && type->IsInt() && type->AsInt()->IsSigned())
      return false;
  }

  return true;
}

/////////////////////////////////////////////////////////////////////
// Solver
/////////////////////////////////////////////////////////////////////

Solver::Solver(const char *name)
  : m_name(name), m_verbose(false), m_base(NULL),
    m_assign_pinned(false), m_satisfiable(true), m_context_count(0),
    m_solve_time(0), m_elapsed_timer(NULL),
    m_constraint_lvalue("Lvalue", this),
    m_constraint_bound("Bound", this),
    m_constraint_terminate("Terminate", this),
    m_constraint_offset("Offset", this),
    m_constraint_buffer_read("BufferRead", this),
    m_constraint_unint_unop("UninterpretedUnop", this),
    m_constraint_unint_binop("UninterpretedBinop", this),
    m_constraint_combine_binop("CombineBinop", this),
    m_constraint_equal_step("EqualityOneStep", this),
    m_constraint_equal_transitive("EqualityTransitive", this)
{
  // check whether to use verbose output.
  const char *verbose_name = solver_verbose.StringValue();

  if (strcmp(verbose_name, m_name) == 0)
    m_verbose = true;
  if (strcmp(verbose_name, "all") == 0)
    m_verbose = true;

  const char *solver_name = solver_use.StringValue();
  if (!strcmp(solver_name,"yices")) {
#ifdef SOLVER_YICES
    m_base = new SolverYices(this);
#else
    logout << "ERROR: Not compiled to use Yices" << endl << flush;
    abort();
#endif
  }
  else if (!strcmp(solver_name,"cvc3")) {
#ifdef SOLVER_CVC3
    m_base = new SolverCVC3(this);
#else
    logout << "ERROR: Not compiled to use CVC3" << endl << flush;
    abort();
#endif
  }
  else if (!strcmp(solver_name,"mux")) {
#ifdef SOLVER_YICES
#ifdef SOLVER_CVC3
    Vector<BaseSolver*> solvers;
    solvers.PushBack(new SolverYices(this));
    solvers.PushBack(new SolverCVC3(this));
    m_base = new SolverMUX(this, solvers);
#else
    logout << "ERROR: Not compiled to use CVC3" << endl << flush;
    abort();
#endif
#else
    logout << "ERROR: Not compiled to use Yices" << endl << flush;
    abort();
#endif
  }
  else {
    logout << "ERROR: Unrecognized solver name: " << solver_name << endl;
    abort();
  }

  // there is always a null frame available.
  m_frames.PushBack(NULL);

  // set up the default listeners for the constraint tables.
  m_constraint_equal_step.RegisterListener(MakeConstraintEqualityStep);
  m_constraint_lvalue.RegisterListener(MakeConstraintLvalue);
  m_constraint_bound.RegisterListener(MakeConstraintBound);
  m_constraint_terminate.RegisterListener(MakeConstraintTerminate);
  m_constraint_offset.RegisterListener(MakeConstraintOffset);
  m_constraint_unint_unop.RegisterListener(MakeConstraintUnintUnop);
  m_constraint_unint_binop.RegisterListener(MakeConstraintUnintBinop);
  m_constraint_combine_binop.RegisterListener(MakeConstraintCombineBinop);
}

void Solver::PrintTimers()
{
  logout << "Solver: " << m_base->Name() << ": ";
  PrintTime(m_solve_time);
  logout << " / ";
  PrintTime(m_elapsed_timer.Elapsed());
  logout << endl;

  m_base->PrintTimers();
}

void Solver::AddAssert(FrameId frame, Bit *bit, bool side_conditions)
{
  // if the bit is a conjunction, break out its operands.
  Vector<Bit*> bit_list;
  if (bit->Kind() == BIT_And) {
    for (size_t ind = 0; ind < bit->GetOperandCount(); ind++)
      bit_list.PushBack(bit->GetOperand(ind));
  }
  else {
    bit_list.PushBack(bit);
  }

  ConvertState state(frame, true);

  for (size_t ind = 0; ind < bit_list.Size(); ind++) {
    Bit *sub_bit = bit_list[ind];

    SlvExpr expr = ConvertBit(state, sub_bit);
    PushAssert(expr);

    SlvExpr *pexpr = m_asserted_bit_table.Lookup(frame, sub_bit, true);
    *pexpr = expr;

    if (m_verbose) {
      logout << "SOLVER: Asserting: " << frame << ": "
             << sub_bit << " [" << sub_bit->Hash() << "]" << endl;
      m_base->PrintRawData(expr, true);
      logout << endl;
    }
  }

  if (side_conditions) {
    SideConditionVisitor side_visitor;
    bit->DoVisit(&side_visitor);

    for (size_t ind = 0; ind < side_visitor.side_list.Size(); ind++) {
      Bit *side_bit = side_visitor.side_list[ind];
      AddConstraint(frame, side_bit);
    }
  }
}

void Solver::AddSideConditions(FrameId frame, Bit *bit)
{
  ConvertState state(frame, true);
  ConvertBit(state, bit);

  // ignore the generated expression, we are only interested in getting
  // the pending expressions used by the bit.

  SideConditionVisitor side_visitor;
  bit->DoVisit(&side_visitor);

  for (size_t ind = 0; ind < side_visitor.side_list.Size(); ind++) {
    Bit *side_bit = side_visitor.side_list[ind];
    AddConstraint(frame, side_bit);
  }
}

void Solver::AddConstraint(FrameId frame, Bit *bit)
{
  ConvertState state(frame, false);
  SlvExpr expr = ConvertBit(state, bit);
  PushAssert(expr);

  if (m_verbose) {
    logout << "SOLVER: Constraint: " << frame << ": " << bit
           << " [" << bit->Hash() << "]" << endl;
    m_base->PrintRawData(expr, true);
    logout << endl;
  }
}

void Solver::AddAssertList(FrameId frame, const GuardBitVector &bit_list,
                           bool side_conditions)
{
  for (size_t ind = 0; ind < bit_list.Size(); ind++) {
    const GuardBit &gb = bit_list[ind];

    if (gb.guard->IsTrue()) {
      AddAssert(frame, gb.bit, side_conditions);
    }
    else {
      Bit *imply_bit = Bit::MakeImply(gb.guard, gb.bit);
      AddAssert(frame, imply_bit);

      if (side_conditions) {
        SideConditionVisitor side_visitor;
        gb.bit->DoVisit(&side_visitor);

        for (size_t ind = 0; ind < side_visitor.side_list.Size(); ind++) {
          Bit *side_bit = side_visitor.side_list[ind];
          Bit *side_imply = Bit::MakeImply(gb.guard, side_bit);
          AddConstraint(frame, side_imply);
        }
      }
    }
  }
}

bool Solver::ExpandVal(FrameId frame, Exp *exp, bool pending)
{
  BlockMemory *mcfg = m_frames[frame];
  Assert(mcfg);

  bool replace = false;
  ExpVal *exp_val = NULL;

  if (ExpVal *nexp = exp->IfVal()) {
    exp_val = nexp;
  }
  else if (exp->IsBound() || exp->IsTerminate()) {
    if (Exp *target = exp->GetLvalTarget()) {
      if (ExpVal *ntarget = target->IfVal()) {
        replace = true;
        exp_val = ntarget;
      }
    }
  }

  if (!exp_val)
    return false;

  if (m_verbose)
    logout << "SOLVER: Expanding ExpVal expression: "
           << frame << ": " << exp << " " << endl;

  Exp *lval = exp_val->GetLvalue();
  Exp *value_kind = exp_val->GetValueKind();
  PPoint point = exp_val->GetPoint();

  // get the actual lvalues being referred to.
  GuardExpVector lval_res;
  if (exp_val->IsRelative()) {
    mcfg->TranslateExp(TRK_Point, point, lval, &lval_res);
  }
  else {
    Bit *true_bit = Bit::MakeConstant(true);
    lval_res.PushBack(GuardExp(lval, true_bit));
  }

  for (size_t lind = 0; lind < lval_res.Size(); lind++) {
    const GuardExp &lv = lval_res[lind];
    const Vector<GuardExp> &values = mcfg->GetVal(lv.exp, value_kind, point);

    for (size_t ind = 0; ind < values.Size(); ind++) {
      const GuardExp &val = values[ind];
      Bit *combine = Bit::MakeAnd(lv.guard, val.guard);
      Exp *use_exp = replace ? exp->ReplaceLvalTarget(val.exp) : val.exp;

      AddEquality(frame, frame,
                  exp, NULL, false,
                  use_exp, combine, pending);
    }
  }

  return true;
}

// return whether a particular exp is always non-NULL, i.e. it indicates the
// stack or static location of a variable or array element.
inline bool NonNullExp(Exp *exp)
{
  // pull off any array indexes.
  while (ExpIndex *nexp = exp->IfIndex())
    exp = nexp->GetTarget();

  if (exp->IsVar() || exp->IsString())
    return true;

  return false;
}

// return whether exp is a useful term to add to the equality constraints.
// for now we are only adding these from AddEquality, e.g. for the expansion
// of val terms and connecting of solver frames, and not appearances
// of B_Equal in the asserted guards.
inline bool IsEqualityTerm(Exp *exp)
{
  return exp->IsInt() || exp->IsLvalue() || exp->IsVal();
}

void Solver::AddEquality(FrameId frame_one, FrameId frame_two,
               Exp *exp_one, Bit *cond_one, bool pending_one,
               Exp *exp_two, Bit *cond_two, bool pending_two)
{
  // these can't both be specified.
  Assert(!pending_one || !pending_two);

  bool cond_one_true;
  if (cond_one)
    cond_one_true = cond_one->IsTrue();
  else
    cond_one_true = true;

  bool cond_two_true;
  if (cond_two)
    cond_two_true = cond_two->IsTrue();
  else
    cond_two_true = true;

  if (IsEqualityTerm(exp_one) && IsEqualityTerm(exp_two)) {
    // add bidirectional equalities, except for constants.
    if (!exp_one->IsInt())
      m_constraint_equal_step.Insert(frame_one, exp_one, frame_two, exp_two);
    if (!exp_two->IsInt())
      m_constraint_equal_step.Insert(frame_two, exp_two, frame_one, exp_one);
  }

  ConvertState state_one(frame_one, pending_one);
  ConvertState state_two(frame_two, pending_two);

  SlvExpr expr_one = ConvertExpIntegral(state_one, exp_one);
  SlvExpr expr_two = ConvertExpIntegral(state_two, exp_two);

  SlvExpr equals_expr = m_base->GetBinop(B_Equal, expr_one, expr_two);

  // check if we should add a non-NULL assumption about one of the exps.
  // this is checking for cases where the address of a variable is taken,
  // which might be compared with NULL in the other frame.
  SlvExpr nonzero_expr = NULL;

  if (NonNullExp(exp_one) && !NonNullExp(exp_two))
    nonzero_expr = expr_one;
  else if (NonNullExp(exp_two) && !NonNullExp(exp_one))
    nonzero_expr = expr_two;

  if (nonzero_expr) {
    SlvExpr zero_expr = m_base->MakeIntegralConstant(0);
    SlvExpr ne_expr = m_base->GetBinop(B_NotEqual, nonzero_expr, zero_expr);
    PushAssert(ne_expr);

    if (m_verbose) {
      logout << "SOLVER: Asserting non-NULL:" << endl;
      m_base->PrintRawData(ne_expr, true);
      logout << endl;
    }
  }

  if (cond_one_true && cond_two_true) {
    // add an unconditional equality between the two expressions.
    PushAssert(equals_expr);

    if (m_verbose) {
      logout << "SOLVER: Asserting equality: "
             << frame_one << " [" << exp_one->Hash() << "] "
             << frame_two << " [" << exp_two->Hash() << "]" << endl;
      m_base->PrintRawData(equals_expr, true);
      logout << endl;
    }
  }
  else {
    // make an implication:
    // (cond_one && cond_two) => (exp_one == exp_two)

    SlvExpr conjunct_expr = NULL;
    if (cond_one_true) {
      conjunct_expr = ConvertBit(state_two, cond_two);
    }
    else if (cond_two_true) {
      conjunct_expr = ConvertBit(state_one, cond_one);
    }
    else {
      SlvExpr cond_expr_one = ConvertBit(state_one, cond_one);
      SlvExpr cond_expr_two = ConvertBit(state_two, cond_two);
      conjunct_expr = m_base->GetBinop(B_LogicalAnd, cond_expr_one, cond_expr_two);
    }

    SlvExpr not_conjunct_expr = m_base->GetUnop(U_LogicalNot, conjunct_expr);
    SlvExpr imply_expr = m_base->GetBinop(B_LogicalOr, not_conjunct_expr, equals_expr);
    PushAssert(imply_expr);

    if (m_verbose) {
      logout << "SOLVER: Asserting conditional equality:" << endl;
      m_base->PrintRawData(imply_expr, true);
      logout << endl;
    }
  }
}

void Solver::GetPendingExps(FrameId frame, Vector<Exp*> *exp_list)
{
  HashIterate(m_expr_pending_table) {
    Assert(m_expr_pending_table.ItFrame() == frame);

    Exp *exp = m_expr_pending_table.ItKey();
    AddHandledExp(frame, exp);

    exp_list->PushBack(exp);
  }

  m_expr_pending_table.Clear();
}

void Solver::GetBitTerms(FrameId frame, Bit *bit, Vector<Exp*> *exp_list)
{
  ConvertState state(frame, false, exp_list);
  ConvertBit(state, bit);
}

void Solver::ExpandPendingVal(FrameId frame)
{
  while (true) {
    Vector<Exp*> exp_list;
    GetPendingExps(frame, &exp_list);

    if (exp_list.Empty())
      break;

    for (size_t ind = 0; ind < exp_list.Size(); ind++) {
      Exp *exp = exp_list[ind];
      ExpandVal(frame, exp);
    }
  }
}

void Solver::CheckAssignmentBits()
{
  Assert(m_assign_pinned);

  // failures here can indicate problems with expression conversion,
  // expression assignments or the solver itself.

  HashIterate(m_asserted_bit_table) {
    FrameId frame = m_asserted_bit_table.ItFrame();
    Bit *bit = m_asserted_bit_table.ItKey();

    bool res;
    AsnBitValue(frame, bit, &res);

    if (!res) {
      logout << "ERROR: Asserted bit does not hold under assignment: #"
             << frame << " " << bit << endl;
      PrintRawAssignment();
      abort();
    }
  }
}

bool Solver::IsSatisfiable(bool expired_result)
{
  static BaseTimer solve_timer("solver_sat");
  Timer _timer(&solve_timer);

  if (m_verbose)
    logout << "SOLVER: Checking" << endl;

  if (TimerAlarm::ActiveExpired()) {
    if (m_verbose)
      logout << "SOLVER: Alarm expired" << endl;
    return expired_result;
  }

  bool result = m_satisfiable ? true : m_base->BaseCheck();
  m_satisfiable = result;

  if (m_verbose)
    logout << "SOLVER: Checking result: " << result << endl;

  uint64_t elapsed = _timer.Elapsed();
  m_solve_time += elapsed;

  // warn on SAT queries taking one second or longer.
  if (elapsed >= 1000000) {
    logout << "WARNING: Long SAT query: ";
    PrintTime(elapsed);
    logout << endl;
  }

  return result;
}

// comparator which will sort keys by the frame they appear in.
class CompareConstraintKeyFrame {
public:
  static int Compare(ConstraintKey *key0, ConstraintKey *key1)
  {
    if (key0->frame < key1->frame)
      return -1;
    if (key0->frame > key1->frame)
      return 1;
    return 0;
  }
};

struct TryUnopInfo
{
  long operand_val;
  long result_val;
};

void GetUnopCandidates(UnopKind unop,
                       const mpz_t operand_val, const mpz_t result_val,
                       Vector<TryUnopInfo> *candidates)
{
}

struct TryBinopInfo
{
  long left_val;
  long right_val;
  long result_val;
};

void GetBinopCandidates(BinopKind binop,
                        const mpz_t left_val, const mpz_t right_val,
                        const mpz_t result_val,
                        Vector<TryBinopInfo> *candidates)
{
  // just get the result of applying the operation to the assignment-generated
  // left and right sides.
  mpz_t new_result_val;
  mpz_init(new_result_val);

  ConstFoldBinop(binop, left_val, right_val, new_result_val);

  if (mpz_fits_slong_p(left_val) && mpz_fits_slong_p(right_val) &&
      mpz_fits_slong_p(result_val)) {
    TryBinopInfo info;
    info.left_val = mpz_get_si(left_val);
    info.right_val = mpz_get_si(right_val);
    info.result_val = mpz_get_si(new_result_val);
    candidates->PushBack(info);
  }

  mpz_clear(new_result_val);
}

void Solver::TryFixUninterpreted()
{
  // disabled for now.
  Assert(false);

  /*
  Assert(IsSatisfiable());

  // all the uninterpreted unops and binops we've generated will be
  // in the constraint tables, so get the keys from them.

  Vector<ConstraintKey*> unop_keys;
  m_constraint_unint_unop.GetKeys(&unop_keys);

  SortVector<ConstraintKey*,CompareConstraintKeyFrame>(&unop_keys);

  for (size_t ind = 0; ind < unop_keys.Size(); ind++) {
    ConstraintKey *key = unop_keys[ind];

    ExpUnop *unop = key->exp->AsUnop();
    Exp *operand = unop->GetOperand();

    mpz_t result_val;
    mpz_init(result_val);

    mpz_t operand_val;
    mpz_init(operand_val);

    PinAssign();
    AsnExpValue(key->frame, unop, result_val);
    AsnExpValue(key->frame, operand, operand_val);
    UnpinAssign();

    Vector<TryUnopInfo> candidates;
    GetUnopCandidates(unop->GetUnopKind(), operand_val, result_val,
                      &candidates);

    bool succeeded = false;
    for (size_t ind = 0; ind < candidates.Size(); ind++) {
      TryUnopInfo info = candidates[ind];
      Exp *operand_int = Exp::MakeInt(info.operand_val);
      Exp *result_int = Exp::MakeInt(info.result_val);

      Bit *operand_equal = Exp::MakeCompareBit(B_Equal, operand, operand_int);
      Bit *unop_equal = Exp::MakeCompareBit(B_Equal, unop, result_int);

      ConvertState state(key->frame, false);
      SlvExpr operand_expr = ConvertBit(state, operand_equal);
      SlvExpr unop_expr = ConvertBit(state, unop_equal);

      m_satisfiable = false;

      SlvAssert operand_id = InternalAssertRetractable(operand_expr);
      SlvAssert unop_id = InternalAssertRetractable(unop_expr);

      if (IsSatisfiable()) {
        succeeded = true;
        break;
      }

      InternalRetractAssert(operand_id);
      InternalRetractAssert(unop_id);
    }

    if (!succeeded)
      logout << "WARNING: Could not find nonlinear assignment: " << unop
             << ": " << operand_val << " -> " << result_val << endl;

    mpz_clear(result_val);
    mpz_clear(operand_val);
  }

  Vector<ConstraintKey*> binop_keys;
  m_constraint_unint_binop.GetKeys(&binop_keys);

  SortVector<ConstraintKey*,CompareConstraintKeyFrame>(&binop_keys);

  for (size_t ind = 0; ind < binop_keys.Size(); ind++) {
    ConstraintKey *key = binop_keys[ind];

    ExpBinop *binop = key->exp->AsBinop();
    Exp *left_exp = binop->GetLeftOperand();
    Exp *right_exp = binop->GetRightOperand();

    // ignore division by a constant, we generate new terms for these but
    // the constraints we add will model them exactly.
    if (binop->GetBinopKind() == B_Div ||
        binop->GetBinopKind() == B_DivExact) {
      if (right_exp->IsInt())
        continue;
    }

    mpz_t result_val;
    mpz_init(result_val);

    mpz_t left_val;
    mpz_init(left_val);

    mpz_t right_val;
    mpz_init(right_val);

    PinAssign();
    AsnExpValue(key->frame, binop, result_val);
    AsnExpValue(key->frame, left_exp, left_val);
    AsnExpValue(key->frame, right_exp, right_val);
    UnpinAssign();

    Vector<TryBinopInfo> candidates;
    GetBinopCandidates(binop->GetBinopKind(), left_val, right_val, result_val,
                       &candidates);

    bool succeeded = false;
    for (size_t ind = 0; ind < candidates.Size(); ind++) {
      TryBinopInfo info = candidates[ind];
      Exp *left_int = Exp::MakeInt(info.left_val);
      Exp *right_int = Exp::MakeInt(info.right_val);
      Exp *result_int = Exp::MakeInt(info.result_val);

      Bit *left_equal = Exp::MakeCompareBit(B_Equal, left_exp, left_int);
      Bit *right_equal = Exp::MakeCompareBit(B_Equal, right_exp, right_int);
      Bit *binop_equal = Exp::MakeCompareBit(B_Equal, binop, result_int);

      ConvertState state(key->frame, false);
      SlvExpr left_expr = ConvertBit(state, left_equal);
      SlvExpr right_expr = ConvertBit(state, right_equal);
      SlvExpr binop_expr = ConvertBit(state, binop_equal);

      m_satisfiable = false;

      SlvAssert left_id = InternalAssertRetractable(left_expr);
      SlvAssert right_id = InternalAssertRetractable(right_expr);
      SlvAssert binop_id = InternalAssertRetractable(binop_expr);

      if (IsSatisfiable()) {
        succeeded = true;
        break;
      }

      InternalRetractAssert(left_id);
      InternalRetractAssert(right_id);
      InternalRetractAssert(binop_id);
    }

    if (!succeeded)
      logout << "WARNING: " << key->frame
             << ": Could not find nonlinear assignment: " << binop
             << ": " << left_val << " " << right_val
             << " -> " << result_val << endl;

    mpz_clear(result_val);
    mpz_clear(left_val);
    mpz_clear(right_val);
  }
  */
}

void Solver::PrintRawAssignment()
{
  Assert(m_assign_pinned);

  logout << "Assignment:" << endl;

  HashIterate(m_assign) {
    const FrameExp &info = m_assign.ItKey();
    logout << "#" << info.frame << " " << info.exp << ": ";

    static Buffer scratch_buf;
    scratch_buf.Reset();

    IntToString(&scratch_buf, m_assign.ItValueSingle().n);
    logout << (const char*) scratch_buf.base << endl;
  }
}

void Solver::Clear()
{
  Assert(!m_assign_pinned);

  m_base->Clear();

  m_satisfiable = true;
  m_context_count = 0;

  if (m_verbose)
    logout << "SOLVER: Clearing [" << m_name << "]" << endl;

  m_decl_table.Clear();
  m_expr_pending_table.Clear();
  m_expr_handled_table.Clear();
  m_asserted_bit_table.Clear();

  for (size_t ind = 0; ind < m_constraint_tables.Size(); ind++)
    m_constraint_tables[ind]->Clear();

  m_frames.Clear();
  m_frames.PushBack(NULL);
}

void Solver::PushContext()
{
  Assert(!m_assign_pinned);

  // only allow pushes when the solver is satisfiable.
  Assert(IsSatisfiable(true));

  m_base->PushContext();

  m_context_count++;

  if (m_verbose) {
    logout << "SOLVER: Pushing context"
           << " [" << m_name << ":" << m_context_count << "]" << endl;

    if (solver_constraint.IsSpecified())
      PrintConstraintTables();
  }

  m_decl_table.PushContext();
  m_expr_handled_table.PushContext();
  m_asserted_bit_table.PushContext();

  // only pending expressions are for the current solver context.
  m_expr_pending_table.Clear();

  for (size_t ind = 0; ind < m_constraint_tables.Size(); ind++)
    m_constraint_tables[ind]->PushContext();
}

void Solver::PopContext()
{
  Assert(!m_assign_pinned);

  m_base->PopContext();

  // we checked at the PushContext() that the constraints were satisfiable.
  m_satisfiable = true;

  m_context_count--;

  m_decl_table.PopContext();
  m_expr_handled_table.PopContext();
  m_asserted_bit_table.PopContext();

  // ditto on pending expressions.
  m_expr_pending_table.Clear();

  for (size_t ind = 0; ind < m_constraint_tables.Size(); ind++)
    m_constraint_tables[ind]->PopContext();

  if (m_verbose) {
    logout << "SOLVER: Popping context"
           << " [" << m_name << ":" << (m_context_count + 1) << "]" << endl;

    if (solver_constraint.IsSpecified())
      PrintConstraintTables();
  }
}

void Solver::PinAssign()
{
  Assert(!m_assign_pinned);
  m_assign_pinned = true;

  static BaseTimer assign_timer("solver_assign");
  Timer _timer(&assign_timer);

  if (m_verbose)
    logout << "SOLVER: Getting assign" << endl;

  m_base->GetAssignment(m_decl_table, m_assign);

  uint64_t elapsed = _timer.Elapsed();
  m_solve_time += elapsed;

  // warn if constructing the assign takes at least one second.
  if (elapsed >= 1000000) {
    logout << "WARNING: Expensive SAT assign generation: ";
    PrintTime(elapsed);
    logout << endl;
  }
}

void Solver::UnpinAssign()
{
  Assert(m_assign_pinned);
  m_assign_pinned = false;

  HashIterate(m_assign)
    mpz_clear(m_assign.ItValueSingle().n);
  m_assign.Clear();
}

void Solver::AsnCheckPointReached(FrameId frame, PPoint point)
{
  BlockMemory *mcfg = m_frames[frame];
  Assert(mcfg);

  Bit *guard = mcfg->GetGuard(point);

  bool guard_value;
  AsnBitValue(frame, guard, &guard_value);
  Assert(guard_value);
}

PEdge* Solver::AsnEdgeTaken(FrameId frame, PPoint point, bool required)
{
  AsnCheckPointReached(frame, point);

  BlockMemory *mcfg = m_frames[frame];
  Assert(mcfg);

  BlockCFG *cfg = mcfg->GetCFG();
  Assert(cfg);

  const Vector<PEdge*> &edges = cfg->GetOutgoingEdges(point);
  if (edges.Empty()) {
    Assert(!required);
    return NULL;
  }

  // there should be exactly one edge that was taken.
  PEdge *taken_edge = NULL;

  for (size_t eind = 0; eind < edges.Size(); eind++) {
    PEdge *edge = edges[eind];
    Bit *edge_cond = mcfg->GetEdgeCond(edge);
    if (edge_cond == NULL) {
      Assert(!taken_edge);
      taken_edge = edge;
    }
    else {
      bool edge_cond_value;
      AsnBitValue(frame, edge_cond, &edge_cond_value);

      if (edge_cond_value) {
        Assert(!taken_edge);
        taken_edge = edge;
      }
    }
  }

  if (!taken_edge) {
    // just pick an edge to use. this will be at the end of the assignment
    // path so it is OK if we didn't track the variables that are only used
    // at the final point in the path.
    Assert(!required);
    return edges[0];
  }

  AsnCheckPointReached(frame, taken_edge->GetTarget());
  return taken_edge;
}

bool Solver::AsnBitValue(FrameId frame, Bit *bit, bool *res)
{
  bool assigned = false;

  switch (bit->Kind()) {
  case BIT_True:
  case BIT_False:
    *res = bit->IsTrue();
    assigned = true;
    break;
  case BIT_Var: {
    mpz_t var_val;
    mpz_init(var_val);

    assigned = AsnExpValue(frame, bit->GetVar(), var_val);
    *res = (mpz_cmp_si(var_val, 0) != 0);

    mpz_clear(var_val);
    break;
  }
  case BIT_Not: {
    bool negbit_value;
    assigned = AsnBitValue(frame, bit->GetOperand(0), &negbit_value);

    *res = !negbit_value;
    break;
  }
  case BIT_And:
  case BIT_Or: {
    // if there are any unassigned bits then the result is unassigned
    // unless one of the operands forces the result to true/false.
    bool has_unassigned = false;

    // default value to use if all the bits are either true (BIT_And) or
    // false (BIT_Or). in this case the result is that value.
    *res = (bit->Kind() == BIT_And);

    Assert(bit->GetOperandCount() >= 2);
    for (size_t oind = 0; oind < bit->GetOperandCount(); oind++) {
      bool bit_value;
      bool sub_assigned =
        AsnBitValue(frame, bit->GetOperand(oind), &bit_value);

      // check if this forces the result to false (BIT_And)
      // or true (BIT_Or).
      if ((bit->Kind() == BIT_Or) == bit_value) {
        *res = bit_value;
        assigned = true;
        break;
      }

      if (!sub_assigned)
        has_unassigned = true;
    }

    // update assigned if it wasn't already set.
    if (!assigned)
      assigned = !has_unassigned;

    break;
  }
  default:
    Assert(false);
    break;
  }

  return assigned;
}

// whether to conver the specified expression by operating on the offsets
// of its operands, rather than on the expression itself. offset computation
// is done for any pointer binop, with the exception of tests against NULL
// or other constants.
static inline bool UseOffsetArithmetic(ExpBinop *exp)
{
  BinopKind binop = exp->GetBinopKind();

  if (!IsPointerBinop(binop))
    return false;

  if (IsCompareBinop(binop)) {
    if (exp->GetLeftOperand()->IsInt())
      return false;
    if (exp->GetRightOperand()->IsInt())
      return false;
  }

  return true;
}

// the specified expression should be converted using frame zero;
// it refers to the same value regardless of the frame it appears in.
inline bool UseZeroFrame(Exp *exp)
{
  if (exp->IsBound() || exp->IsTerminate()) {
    Exp *target = exp->GetLvalTarget();

    // absolute bounds/terminators.
    if (target == NULL)
      return true;

    // offsets for global variables.
    if (ExpVar *ntarget = target->IfVar()) {
      if (ntarget->GetVariable()->IsGlobal())
        return true;
    }
  }

  // addresses of global variables.
  if (ExpVar *nexp = exp->IfVar()) {
    if (nexp->GetVariable()->IsGlobal())
      return true;
  }

  return false;
}

bool Solver::AsnExpValue(FrameId frame, Exp *exp, mpz_t res)
{
  Assert(m_assign_pinned);

  if (UseZeroFrame(exp))
    frame = 0;

  // check for a declaration for this exp. this covers expressions that are
  // always uninterpreted as well as unintepreted unops and binops,
  // for which we want to make sure we get the exact value assigned by
  // the solver, not the constant folded value.
  SlvDecl *pdecl = m_decl_table.Lookup(frame, exp, false);

  if (pdecl) {
    Assert(*pdecl);

    FrameExp info(frame, exp);
    Vector<mpz_value> *values = m_assign.Lookup(info);

    if (values) {
      Assert(values->Size() == 1);
      mpz_set(res, values->At(0).n);
      return true;
    }
    return false;
  }

  // for bound expressions, check to see if we have a different declaration
  // we can use to express this bound.
  if (ExpBound *nexp = exp->IfBound()) {
    BoundKind kind = nexp->GetBoundKind();
    Exp *target = nexp->GetTarget();
    ConstraintKey *key = m_constraint_bound.LookupKey(frame, target);

    if (key && (kind == BND_Offset || target == NULL)) {
      ConstraintEntry *entry = key->entries_begin;
      while (entry) {
        ExpBound *exp_bound = entry->exp->AsBound();

        if (Exp *equal = GetBoundEquivalent(nexp, exp_bound)) {
          if (AsnExpValue(frame, equal, res))
            return true;
        }

        entry = entry->key_next;
      }
    }
  }

  Type *offset_type;
  Exp *offset_upper;
  GetExpOffset(exp, &offset_type, &offset_upper);

  if (offset_type) {
    Exp *target = exp->GetLvalTarget();

    if (target && offset_upper) {
      mpz_t base_val;
      mpz_init(base_val);
      bool base_asn = AsnOffset(frame, target, offset_type, base_val);

      mpz_t upper_val;
      mpz_init(upper_val);
      bool upper_asn = AsnExpValue(0, offset_upper, upper_val);

      ConstFoldBinop(B_Minus, upper_val, base_val, res);

      mpz_clear(base_val);
      mpz_clear(upper_val);

      return base_asn && upper_asn;
    }
    else {
      // processing an offset or absolute bound which was never
      // assigned a value. use the default value of 0.
      return false;
    }
  }

  if (IsTermExp(exp)) {
    // can get here only if we never saw the lvalue so never assigned a value
    // to it. just use the default value of 0.
    return false;
  }

  switch (exp->Kind()) {

  case EK_Int: {
    ExpInt *nexp = exp->AsInt();

    nexp->GetMpzValue(res);
    return true;
  }

  case EK_Unop: {
    ExpUnop *nexp = exp->AsUnop();
    UnopKind unop = nexp->GetUnopKind();
    Exp *operand = nexp->GetOperand();

    mpz_t op_val;
    mpz_init(op_val);

    bool assigned = AsnExpValue(frame, operand, op_val);
    ConstFoldUnop(unop, op_val, res);

    mpz_clear(op_val);
    return assigned;
  }

  case EK_Binop: {
    ExpBinop *nexp = exp->AsBinop();
    Exp *left_op = nexp->GetLeftOperand();
    Exp *right_op = nexp->GetRightOperand();

    // convert any pointer binops to their base arithmetic binops.
    BinopKind binop = NonPointerBinop(nexp->GetBinopKind());

    if (UseOffsetArithmetic(nexp)) {
      Type *type = nexp->GetStrideType();
      Assert(type);

      mpz_t left_offset;
      mpz_init(left_offset);

      mpz_t right_offset;
      mpz_init(right_offset);

      bool left_asn = AsnOffset(frame, left_op, type, left_offset);
      bool right_asn = AsnOffset(frame, right_op, type, right_offset);

      ConstFoldBinop(binop, left_offset, right_offset, res);

      mpz_clear(left_offset);
      mpz_clear(right_offset);
      return left_asn && right_asn;
    }

    mpz_t left_val;
    mpz_init(left_val);

    mpz_t right_val;
    mpz_init(right_val);

    bool left_asn = AsnExpValue(frame, left_op, left_val);
    bool right_asn = AsnExpValue(frame, right_op, right_val);

    ConstFoldBinop(binop, left_val, right_val, res);

    mpz_clear(left_val);
    mpz_clear(right_val);
    return left_asn && right_asn;
  }

  case EK_Float:
    // never saw this float, treat as zero.
    return false;

  case EK_Val: {
    ExpVal *nexp = exp->IfVal();

    // never saw this use of val, but we can still get its assigned value.
    BlockMemory *mcfg = m_frames[frame];
    Assert(mcfg);

    // get the lvalue being referred to.
    Exp *lval = NULL;
    if (nexp->IsRelative()) {
      GuardExpVector lval_list;
      mcfg->TranslateExp(TRK_Point, nexp->GetPoint(),
                         nexp->GetLvalue(), &lval_list);
      lval = AsnChooseExp(frame, lval_list);
    }
    else {
      lval = nexp->GetLvalue();
    }

    // get the possible values of the lvalue at the point.
    const Vector<GuardExp> &values =
      mcfg->GetVal(lval, nexp->GetValueKind(), nexp->GetPoint());

    GuardExpVector val_list;
    val_list.FillFromVector(values);
    Exp *exp = AsnChooseExp(frame, val_list);

    return AsnExpValue(frame, exp, res);
  }

  case EK_Frame: {
    ExpFrame *nexp = exp->AsFrame();
    Exp *base_exp= nexp->GetValue();
    FrameId new_frame = nexp->GetFrameId();

    return AsnExpValue(new_frame, base_exp, res);
  }

  default:
    break;
  }

  Assert(false);
  return false;
}

Exp* Solver::AsnChooseExp(FrameId frame, const GuardExpVector &vals)
{
  Exp *res = NULL;

  for (size_t vind = 0; vind < vals.Size(); vind++) {
    const GuardExp &gs = vals[vind];

    bool guard_value;
    AsnBitValue(frame, gs.guard, &guard_value);

    if (guard_value) {
      Assert(res == NULL);
      res = gs.exp;
    }
  }

  Assert(res);
  return res;
}

void Solver::PrintUnsatCore()
{
  m_base->PrintUnsatCore();
}

void Solver::PrintExp(FrameId frame, Exp *exp)
{
  ConvertState state(frame, false);
  SlvExpr expr = ConvertExp(state, exp);
  m_base->PrintRawData(expr, IsBoolean(exp));
  logout << endl;
}

void Solver::PrintBit(FrameId frame, Bit *bit)
{
  ConvertState state(frame, false);
  SlvExpr expr = ConvertBit(state, bit);
  m_base->PrintRawData(expr, true);
  logout << endl;
}

void Solver::PushAssert(SlvExpr expr)
{
  Assert(!m_assign_pinned);

  static BaseTimer assert_timer("solver_assert");
  Timer _timer(&assert_timer);

  m_satisfiable = false;
  m_base->BaseAssert(expr);

  m_solve_time += _timer.Elapsed();
}

SlvExpr Solver::ConvertBit(const ConvertState &state, Bit *bit)
{
  // watch for reentrant conversion (this should only come up if we've turned
  // on checking of exp/bit simplifications).

  SlvExpr res;

  if (Bit::g_extra_used) {
    res = RecursiveConvertBit(state, bit, true);
  }
  else {
    Bit::g_extra_used = true;
    res = RecursiveConvertBit(state, bit, false);
    Bit::g_extra_used = false;
    bit->ClearExtra();
  }

  return res;
}

SlvExpr Solver::RecursiveConvertBit(const ConvertState &state, Bit *bit,
                                    bool revisit)
{
  if (!revisit) {
    Assert(Bit::g_extra_used);

    // use the m_extra field to store the result of translating the bit.
    if (bit->m_extra)
      return (SlvExpr) bit->m_extra;
  }

  BitKind kind = bit->Kind();
  SlvExpr res = NULL;

  switch (kind) {

  case BIT_True: {
    res = m_base->MakeBooleanConstant(true);
    break;
  }

  case BIT_False: {
    res = m_base->MakeBooleanConstant(false);
    break;
  }

  case BIT_Var: {
    res = ConvertExp(state, bit->GetVar());

    // if the variable does not already have a boolean result,
    // get a new value for (res != 0)
    if (!IsBoolean(bit->GetVar()))
      res = m_base->CoerceIntToBool(res, true);
    break;
  }

  case BIT_Not: {
    Bit *neg_bit = bit->GetOperand(0);

    if (neg_bit->Kind() == BIT_Var && !IsBoolean(neg_bit->GetVar())) {
      // use (x == 0) instead of !(x /= 0)
      SlvExpr base_res = ConvertExp(state, neg_bit->GetVar());
      res = m_base->CoerceIntToBool(base_res, false);
    }
    else {
      SlvExpr neg_res = RecursiveConvertBit(state, neg_bit, revisit);
      res = m_base->GetUnop(U_LogicalNot, neg_res);
    }

    break;
  }

  case BIT_And:
  case BIT_Or: {
    BinopKind binop = (kind == BIT_And) ? B_LogicalAnd : B_LogicalOr;

    // we will handle degenerate 0 and 1 operand cases here; these will only
    // show up when checking the correctness of bit simplifications.
    size_t op_count = bit->GetOperandCount();

    for (size_t oind = 0; oind < op_count; oind++) {
      Bit *op = bit->GetOperand(oind);
      SlvExpr op_expr = RecursiveConvertBit(state, op, revisit);

      if (res)
        res = m_base->GetBinop(binop, res, op_expr);
      else
        res = op_expr;

      if (!res)
        res = m_base->MakeBooleanConstant(kind == BIT_And);
    }

    break;
  }

  default:
    Assert(false);
  }

  Assert(res);

  if (!revisit)
    bit->m_extra = res;

  return res;
}

void Solver::GetExpOffset(Exp *exp, Type **offset_type, Exp **offset_upper)
{
  *offset_type = NULL;
  *offset_upper = NULL;

  bool has_target = (exp->GetLvalTarget() != NULL);

  if (ExpBound *nexp = exp->IfBound()) {
    *offset_type = nexp->GetStrideType();
    BoundKind bound = nexp->GetBoundKind();

    // leave offset_upper as NULL for BND_Offset, we will not do a difference.
    if (bound != BND_Offset && has_target)
      *offset_upper = exp->ReplaceLvalTarget(NULL);
  }

  if (ExpTerminate *nexp = exp->IfTerminate()) {
    *offset_type = nexp->GetStrideType();

    if (has_target)
      *offset_upper = exp->ReplaceLvalTarget(NULL);
  }
}

SlvExpr Solver::ConvertExp(const ConvertState &state, Exp *exp)
{
  Type *offset_type;
  Exp *offset_upper;
  GetExpOffset(exp, &offset_type, &offset_upper);

  if (offset_type) {
    Exp *target = exp->GetLvalTarget();

    // for ubounds and terminators we will add both the offset and the
    // bound/terminator itself. this is needed for terminators since they
    // are a flow sensitive property, and is helpful for the UI for ubounds.
    if (target)
      AddPendingExp(state, exp);

    if (exp->IsBound()) {
      // strip trailing indexes off of bound targets.
      Exp *new_target = target;
      while (new_target && new_target->IsIndex())
        new_target = new_target->GetLvalTarget();
      m_constraint_bound.Insert(state.frame, new_target, state.frame, exp);

      if (exp->AsBound()->GetBoundKind() == BND_Offset) {
        Exp *key = exp->ReplaceLvalTarget(NULL);
        m_constraint_offset.Insert(0, key, state.frame, exp);
      }
    }
    else if (exp->IsTerminate()) {
      m_constraint_terminate.Insert(state.frame, target, state.frame, exp);
    }
    else {
      Assert(false);
    }

    if (target) {
      // relative bound/terminate which we will model as the difference
      // from an absolute bound/terminate.

      SlvExpr offset_base = ConvertOffset(state, target, offset_type);
      if (offset_upper) {
        ConvertState abs_state(0, false);
        SlvExpr offset_expr = ConvertExp(abs_state, offset_upper);
        return m_base->GetBinop(B_Minus, offset_expr, offset_base);
      }
      else {
        return offset_base;
      }
    }
    else {
      // absolute bound/terminate. make a declaration for this expression.
      SlvDecl decl = GetDeclaration(state, exp, NULL);
      return m_base->GetDeclarationExpr(decl);
    }
  }

  if (IsTermExp(exp)) {
    // make a variable declaration for the lvalue.
    bool exists;
    SlvDecl decl = GetDeclaration(state, exp, &exists);
    SlvExpr res = m_base->GetDeclarationExpr(decl);

    if (!exists) {
      m_constraint_lvalue.Insert(state.frame, exp, state.frame, exp);

      // check if this can be treated as a buffer read.
      if (ExpDrf *nexp = exp->IfDrf()) {
        Exp *lval = nexp->GetTarget();

        while (ExpFld *nlval = lval->IfFld())
          lval = nlval->GetTarget();

        // match against *p and p[?] lvalues.
        Exp *base = NULL;
        if (lval->IsDrf())
          base = lval;
        else if (lval->IsIndex())
          base = lval->AsIndex()->GetTarget();

        if (base)
          m_constraint_buffer_read.Insert(state.frame, base, state.frame, lval);
      }
    }

    return res;
  }

  SlvExpr res = NULL;

  switch (exp->Kind()) {

  case EK_Int: {
    // make an integral constant.
    mpz_t val;
    mpz_init(val);

    exp->AsInt()->GetMpzValue(val);
    res = m_base->MakeIntegralConstantMpz(val);

    mpz_clear(val);
    break;
  }

  case EK_Unop: {
    ExpUnop *nexp = exp->AsUnop();
    UnopKind unop = nexp->GetUnopKind();
    Exp *op = nexp->GetOperand();

    // watch for logical operations on unops.
    if (unop == U_LogicalNot) {
      SlvExpr op_res = ConvertExp(state, op);

      // get the negation depending on whether the operand is logical.
      if (IsBoolean(op))
        res = m_base->GetUnop(U_LogicalNot, op_res);
      else
        res = m_base->CoerceIntToBool(op_res, false);
      break;
    }

    SlvExpr op_res = ConvertExpIntegral(state, op);

    // check if we are leaving this unop uninterpreted.
    bool uninterpreted = false;
    switch (unop) {
      // operations which are always interpreted exactly.
    case U_Coerce:
    case U_Neg:
      break;
      // operations we always leave uninterpreted (with any side constraints).
    case U_BitwiseNot:
      uninterpreted = true;
      break;
    default:
      Assert(false);
    }

    if (uninterpreted) {
      res = m_base->GetUninterpretedUnop(unop, op_res);

      ConvertState empty_state(state.frame, false);

      // make a declaration to remember the value of the application.
      bool exists;
      SlvDecl decl = GetDeclaration(empty_state, exp, &exists);
      SlvExpr decl_expr = m_base->GetDeclarationExpr(decl);

      if (!exists) {
        SlvExpr equal_expr = m_base->GetBinop(B_Equal, res, decl_expr);
        PushAssert(equal_expr);

        m_constraint_unint_unop.Insert(state.frame, exp, state.frame, exp);
      }
    }
    else if (unop == U_Coerce) {
      // coercions are always treated as nops for now.
      res = op_res;
    }
    else {
      res = m_base->GetUnop(unop, op_res);
    }

    break;
  }

  case EK_Binop: {
    ExpBinop *nexp = exp->AsBinop();
    Exp *left_op = nexp->GetLeftOperand();
    Exp *right_op = nexp->GetRightOperand();
    Type *type = nexp->GetStrideType();

    BinopKind binop = NonPointerBinop(nexp->GetBinopKind());

    // watch for logical and/or on booleans.
    if (IsLogicalBinop(binop)) {
      SlvExpr left_res = ConvertExp(state, left_op);
      SlvExpr right_res = ConvertExp(state, right_op);

      // make sure both operands are boolean.
      if (!IsBoolean(left_op))
        left_res = m_base->CoerceIntToBool(left_res, true);
      if (!IsBoolean(right_op))
        right_res = m_base->CoerceIntToBool(right_res, true);

      res = m_base->GetBinop(binop, left_res, right_res);
      break;
    }

    // handle pointer binops (MinusPP and comparisons) as operations on
    // the offsets of the left and right sides.
    if (UseOffsetArithmetic(nexp)) {
      Assert(type);

      SlvExpr left_res = ConvertOffset(state, left_op, type);
      SlvExpr right_res = ConvertOffset(state, right_op, type);

      res = m_base->GetBinop(binop, left_res, right_res);
      break;
    }

    // get the plain integral values of the operands.

    SlvExpr left_res = ConvertExpIntegral(state, left_op);
    SlvExpr right_res = ConvertExpIntegral(state, right_op);

    // check if we are leaving this binop uninterpreted.
    bool uninterpreted = false;
    switch (binop) {
      // operations which are always interpreted exactly.
    case B_LessThan:
    case B_GreaterThan:
    case B_LessEqual:
    case B_GreaterEqual:
    case B_Equal:
    case B_NotEqual:
    case B_Plus:
    case B_Minus:
    case B_Max:
    case B_Min:
      break;
      // modelled exactly if either operand is an integer.
    case B_Mult:
      if (left_op->IsInt() || right_op->IsInt())
        break;
      uninterpreted = true;
      break;
      // operations we always leave uninterpreted (with any side constraints).
    case B_Div:
    case B_DivExact:
    case B_Mod:
    case B_ShiftLeft:
    case B_ShiftRight:
    case B_BitwiseAnd:
    case B_BitwiseOr:
    case B_BitwiseXOr:
    case B_PlusPI:
    case B_MinusPI:
    case B_MinusPP:
      uninterpreted = true;
      break;
    default:
      // other types of binops should not show up here.
      Assert(false);
    }

    if (uninterpreted) {
      res = m_base->GetUninterpretedBinop(binop, left_res, right_res);

      ConvertState empty_state(state.frame, false);

      // make a declaration to remember the value of the application.
      bool exists;
      SlvExpr decl = GetDeclaration(empty_state, exp, &exists);
      SlvExpr decl_expr = m_base->GetDeclarationExpr(decl);

      if (!exists) {
        SlvExpr equal_expr = m_base->GetBinop(B_Equal, res, decl_expr);
        PushAssert(equal_expr);

        m_constraint_unint_binop.Insert(state.frame, exp, state.frame, exp);

        // make a binop application with empty expressions on the lhs/rhs.
        // this is a combine key which will collect all applications of the
        // same binop within some frame.
        Exp *empty_exp = Exp::MakeEmpty();
        Exp *base_exp = Exp::MakeBinop(binop, empty_exp, empty_exp);

        m_constraint_combine_binop.Insert(state.frame, base_exp, state.frame, exp);
      }
    }
    else {
      res = m_base->GetBinop(binop, left_res, right_res);
    }

    break;
  }

  case EK_Float:
  case EK_Val:
  case EK_GCSafe: {
    // make an unconstrained variable for the expression.
    SlvDecl decl = GetDeclaration(state, exp, NULL);
    res = m_base->GetDeclarationExpr(decl);
    break;
  }

  case EK_Frame: {
    ExpFrame *nexp = exp->AsFrame();
    Exp *base_exp= nexp->GetValue();
    FrameId new_frame = nexp->GetFrameId();

    ConvertState new_state(new_frame, false);

    res = ConvertExp(new_state, base_exp);
    break;
  }

  default:
    logout << "ERROR: ConvertExp: Unexpected expression: " << exp << endl;
    Assert(false);
    break;
  }

  Assert(res);
  return res;
}

SlvExpr Solver::ConvertExpIntegral(const ConvertState &state, Exp *exp)
{
  if (IsBoolean(exp)) {
    SlvExpr bool_res = ConvertExp(state, exp);
    SlvExpr res = m_base->CoerceBoolToInt(bool_res);
    return res;
  }
  else {
    return ConvertExp(state, exp);
  }
}

SlvExpr Solver::ConvertOffset(const ConvertState &state, Exp *lval, Type *type)
{
  Exp *offset = Exp::MakeBound(BND_Offset, lval, type);

  SlvExpr res;

  if (offset->IsBound()) {
    bool exists;
    SlvDecl decl = GetDeclaration(state, offset, &exists);
    res = m_base->GetDeclarationExpr(decl);

    if (!exists) {
      // this target might be different from lval for, e.g. lval == buf[0].
      Exp *new_target = offset->GetLvalTarget();
      while (new_target && new_target->IsIndex())
        new_target = new_target->GetLvalTarget();
      m_constraint_bound.Insert(state.frame, new_target, state.frame, offset);
    }
  }
  else {
    res = ConvertExp(state, offset);
  }

  return res;
}

bool Solver::AsnOffset(FrameId frame, Exp *lval, Type *type, mpz_t res)
{
  Exp *offset = Exp::MakeBound(BND_Offset, lval, type);
  return AsnExpValue(frame, offset, res);
}

SlvDecl Solver::GetDeclaration(const ConvertState &state,
                               Exp *exp, bool *pexists)
{
  FrameId frame = state.frame;

  if (UseZeroFrame(exp))
    frame = 0;

  SlvDecl *pdecl = m_decl_table.Lookup(frame, exp, true);

  // don't add pending for constant float expressions.
  if (!exp->IsFloat())
    AddPendingExp(state, exp);

  if (pexists)
    *pexists = (*pdecl != NULL);

  if (*pdecl == NULL)
    *pdecl = m_base->MakeDeclaration(frame, exp);

  return *pdecl;
}

void Solver::PrintConstraintTables() const
{
  for (size_t ind = 0; ind < m_constraint_tables.Size(); ind++) {
    ConstraintTable *table = m_constraint_tables[ind];
    if (!table->IsEmpty())
      table->Print();
  }
}

NAMESPACE_XGILL_END
