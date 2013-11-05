
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

#include "invariant.h"

#include "expand.h"
#include "nullterm.h"
#include <solve/solver.h>
#include <memory/mstorage.h>

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// invariants utility
/////////////////////////////////////////////////////////////////////

ConfigOption print_invariants(CK_Flag, "print-invariants", NULL,
               "print candidate invariants on loops and functions");

// state maintained by LoopInvariantTester for each point where
// candidate invariants are tested.
struct LoopInvariantPoint
{
  // memory for this point.
  BlockMemory *mcfg;

  // point being tested.
  PPoint point;

  // solver frame for queries on this point.
  size_t frame;

  LoopInvariantPoint()
    : mcfg(NULL), point(0), frame(0)
  {}
};

// structure for testing candidate invariants on a loop or function
// and only adding the true invariants to the underlying summary.
struct InvariantTester
{
  // summary for the loop/func being filled in.
  BlockSummary *sum;

  // bits we have already tested for inclusion in the summary.
  Vector<Bit*> tested_bits;

  // solver we will use to query whether invariants hold.
  Solver *solver;

  // information for testing invariants at the exit point of the loop/func.
  LoopInvariantPoint exit_test;

  // assumptions made when testing the loop/func body. these include the
  // guard at exit from the body and assumptions from invariants on callers
  // or callees.
  Vector<Bit*> assumed_bits;

  // for loop invariants, information for each of the loop's parents.
  // this is non-empty iff we are testing a loop invariant.
  Vector<LoopInvariantPoint> parent_tests;

  // whether this represents a loop/func capable of executing. for loops there
  // must be a parent where the loop can be entered, and for loops/funcs the
  // exit point must be reachable. don't infer anything for inconsistent
  // loops and functions.
  bool consistent;

  // fill in this tester from the specified summary.
  InvariantTester(BlockSummary *_sum)
  {
    consistent = true;

    sum = _sum;

    BlockCFG *cfg = sum->GetMemory()->GetCFG();

    solver = new Solver("invariant");

    exit_test.mcfg = sum->GetMemory();
    exit_test.point = cfg->GetExitPoint();
    exit_test.frame = solver->MakeFrame(exit_test.mcfg);

    if (exit_test.point == 0) {
      consistent = false;
      return;
    }

    for (size_t ind = 0; ind < cfg->GetLoopParentCount(); ind++) {
      BlockPPoint parent = cfg->GetLoopParent(ind);

      BlockMemory *parent_mcfg = GetBlockMemory(parent.id);
      if (parent_mcfg == NULL)
        continue;

      LoopInvariantPoint parent_test;
      parent_test.mcfg = parent_mcfg;
      parent_test.point = parent.point;
      parent_test.frame = solver->MakeFrame(parent_mcfg);

      Bit *entry_guard = parent_test.mcfg->GetGuard(parent_test.point);

      // check the parent is statically reachable. sometimes there
      // are loops that aren't, due to unsoundness or not.
      if (entry_guard->IsFalse()) {
        // skip this parent.
        continue;
      }

      // assert the guard at entry holds for the parent test.
      solver->AddAssert(parent_test.frame, entry_guard);
      solver->ExpandPendingVal(parent_test.frame);

      parent_tests.PushBack(parent_test);
    }

    // fill in assumed bits from existing invariants and annotations on
    // the block and its callees.
    Vector<AssumeInfo> assume_list;
    BlockSummary::GetAssumedBits(sum->GetMemory(), 0, &assume_list);

    for (size_t ind = 0; ind < assume_list.Size(); ind++) {
      const AssumeInfo &info = assume_list[ind];
      assumed_bits.PushBack(info.bit);
    }

    // also assume the loop body exit guards holds for the exit test.
    Bit *exit_guard = exit_test.mcfg->GetGuard(exit_test.point);

    assumed_bits.PushBack(exit_guard);

    for (size_t ind = 0; ind < assumed_bits.Size(); ind++)
      solver->AddAssert(exit_test.frame, assumed_bits[ind]);
    solver->ExpandPendingVal(exit_test.frame);

    // make sure the system is consistent. any condition we try to infer
    // for an inconsistent system will otherwise be marked as an invariant.
    if (!solver->IsSatisfiable())
      consistent = false;
  }

  // clear out this tester.
  ~InvariantTester()
  {
    solver->PrintTimers();
    solver->Clear();
    delete solver;
  }

  // add a candidate invariant for the summary. consumes a reference on bit.
  // returns whether the candidate is in fact an invariant. to be added to the
  // summary bit must meet the following criteria:
  // - not trivially true.
  // - does not reference bad data (clobbered values, temp vars, etc.)
  // - for loops, holds at initial loop entry and after each iteration.
  // - for functions, holds at exit from the function.
  bool AddCandidateInvariant(Bit *bit)
  {
    Assert(bit);

    if (tested_bits.Contains(bit))
      return false;

    tested_bits.PushBack(bit);

    if (print_invariants.IsSpecified())
      logout << "INVARIANT: Testing "
             << bit << " [" << bit->Hash() << "]" << endl;

    if (!consistent) {
      if (print_invariants.IsSpecified())
        logout << "INVARIANT: System is inconsistent" << endl;
      return false;
    }

    bool is_function = (sum->GetId()->Kind() == B_Function);

    if (!UseCallerBit(bit, is_function)) {
      if (print_invariants.IsSpecified())
        logout << "INVARIANT: Not caller visible" << endl;
      return false;
    }

    bool satisfiable;

    if (Solver::BitValid(bit)) {
      // definitely an invariant, just not a useful one.
      if (print_invariants.IsSpecified())
        logout << "INVARIANT: Bit is tautological" << endl;
      return true;
    }

    Bit *not_bit = Bit::MakeNot(bit);

    // check that the bit holds at initial entry to the loop.
    for (size_t ind = 0; ind < parent_tests.Size(); ind++) {
      const LoopInvariantPoint &parent_test = parent_tests[ind];

      solver->PushContext();

      GuardBitVector not_entry_list;
      parent_test.mcfg->TranslateBit(TRK_Callee, parent_test.point,
                                     not_bit, &not_entry_list);
      solver->AddAssertList(parent_test.frame, not_entry_list, true);

      solver->ExpandPendingVal(parent_test.frame);
      satisfiable = solver->IsSatisfiable();

      if (satisfiable && print_invariants.IsSpecified()) {
        logout << "INVARIANT: Does not hold at entry:" << endl;
        solver->PrintRawAssignment();
      }

      solver->PopContext();

      if (satisfiable)
        return false;
    }

    solver->PushContext();

    // conditional bits to assert at exit from the loop/function.
    GuardBitVector not_exit_list;

    if (sum->GetId()->Kind() == B_Loop) {
      // check that the bit holds at exit from each iteration, by induction.

      // assert the bit holds at the beginning of the iteration.
      solver->AddAssert(exit_test.frame, bit);

      // assert the bit does not hold at the end of the iteration.
      exit_test.mcfg->TranslateBit(TRK_Point, exit_test.point,
                                   not_bit, &not_exit_list);
    }
    else {
      // check that the bit holds at exit from the function.

      // translation works different with functions vs. loops. function
      // invariants use ExitDrf explicitly to describe the exit state.

      // assert the bit does not hold at function exit.
      exit_test.mcfg->TranslateBit(TRK_Exit, exit_test.point,
                                   not_bit, &not_exit_list);
    }

    solver->AddAssertList(exit_test.frame, not_exit_list, true);

    solver->ExpandPendingVal(exit_test.frame);
    satisfiable = solver->IsSatisfiable();

    if (satisfiable && print_invariants.IsSpecified()) {
      logout << "INVARIANT: Is not preserved by body:" << endl;

      for (size_t ind = 0; ind < not_exit_list.Size(); ind++) {
        const GuardBit &gb = not_exit_list[ind];
        logout << "Exit: " << gb.bit << endl;
      }

      logout << "Assignment:" << endl;
      solver->PrintRawAssignment();
    }

    solver->PopContext();

    if (satisfiable)
      return false;

    // this is an invariant, so add it to the summary.

    if (print_invariants.IsSpecified())
      logout << "INVARIANT: Success!" << endl;

    sum->AddAssume(bit);

    // also assert it within the solver, in case later invariants need it.
    solver->AddAssert(exit_test.frame, bit);

    if (!solver->IsSatisfiable())
      consistent = false;

    return true;
  }
};

/////////////////////////////////////////////////////////////////////
// comparison inference
/////////////////////////////////////////////////////////////////////

static inline void AddCompare(Vector<BaseCompare> *compares,
                              Exp *test, BinopKind kind,
                              Exp *source, Exp *target, Type *stride_type)
{
  // filter out some comparisons we aren't interested in.

  // ignore comparisons of pointers with zero.
  if (stride_type && target->IsInt())
    return;

  // ignore comparisons of bounds with zero.
  if (source->IsBound() && target->IsInt())
    return;

  Assert(IsPointerBinop(kind) == (stride_type != NULL));

  BaseCompare cmp(test, kind, source, target, stride_type);

  if (!compares->Contains(cmp))
    compares->PushBack(cmp);
}

// visitor to find bits which contain Exit subexpressions. TODO: this is a hack
// and the bits pulled in for compares needs to be cleaned up.
class HasExitVisitor : public ExpVisitor
{
public:
  bool has_exit;

  HasExitVisitor()
    : ExpVisitor(VISK_All), has_exit(false)
  {}

  void Visit(Exp *exp)
  {
    if (exp->IsExit())
      has_exit = true;
  }
};

// visitor to get all the comparisons mentioned in the leaf vars of a bit.
class BaseCompareVisitor : public ExpVisitor
{
 public:
  BlockMemory *mcfg;
  Vector<BaseCompare> *compares;

  BaseCompareVisitor(BlockMemory *_mcfg, Vector<BaseCompare> *_compares,
                     bool ignore_disjunction)
    : ExpVisitor(VISK_BitLeaf), mcfg(_mcfg), compares(_compares)
  {
    m_ignore_disjunction = ignore_disjunction;
  }

  void VisitCompare(Exp *test, BinopKind kind,
                    Exp *left, Exp *right, Type *stride_type)
  {
    if (left->IsLvalue() || left->IsBound() || left->IsTerminate())
      AddCompare(compares, test, kind, left, right, stride_type);

    if (ExpIndex *nleft = left->IfIndex()) {
      // subtract the index from the other side as if this was B_PlusPI.
      Exp *target = nleft->GetTarget();
      Type *type = nleft->GetElementType();
      Exp *index = nleft->GetIndex();

      Exp *new_right = Exp::MakeBinop(B_MinusPI, right, index, type);
      AddCompare(compares, test, kind, target, new_right, stride_type);
    }

    if (ExpBinop *nleft = left->IfBinop()) {
      Exp *left_op = nleft->GetLeftOperand();
      Exp *right_op = nleft->GetRightOperand();
      Type *type = nleft->GetStrideType();
      BinopKind left_kind = nleft->GetBinopKind();

      // expressions to compare left_op and right_op with.
      Exp *compare_left = NULL;
      Exp *compare_right = NULL;

      if (left_kind == B_Plus) {
        compare_left = Exp::MakeBinop(B_Minus, right, right_op);
        compare_right = Exp::MakeBinop(B_Minus, right, left_op);
      }

      if (left_kind == B_Minus) {
        compare_left = Exp::MakeBinop(B_Plus, right, right_op);
        compare_right = Exp::MakeBinop(B_Minus, left_op, right);
      }

      if (left_kind == B_MinusPP) {
        compare_left = Exp::MakeBinop(B_PlusPI, right_op, right, type);
        compare_right = Exp::MakeBinop(B_MinusPI, left_op, right, type);
      }

      // perform scaling if the left side is a constant multiplication.
      if (left_kind == B_Mult && left_op->IsInt())
        compare_right = Exp::MakeBinop(B_Div, right, left_op, type);
      if (left_kind == B_Mult && right_op->IsInt())
        compare_left = Exp::MakeBinop(B_Div, right, right_op, type);

      if (compare_left)
        VisitCompare(test, kind, left_op, compare_left, stride_type);

      if (compare_right)
        VisitCompare(test, kind, right_op, compare_right, stride_type);

      if (!compare_left && !compare_right) {
        // treat as if this were an lvalue.
        AddCompare(compares, test, kind, left, right, stride_type);
      }
    }
  }

  void Visit(Exp *exp)
  {
    // remove ExpVal expressions if possible.
    GuardExpVector exp_res;

    if (mcfg) {
      mcfg->TranslateExp(TRK_TryRemoveVal, 0, exp, &exp_res);
    }
    else {
      Bit *guard = Bit::MakeConstant(true);
      exp_res.PushBack(GuardExp(exp, guard));
    }

    for (size_t ind = 0; ind < exp_res.Size(); ind++) {
      Exp *test_exp = exp_res[ind].exp;

      if (ExpBinop *ntest_exp = test_exp->IfBinop()) {
        Exp *left = ntest_exp->GetLeftOperand();
        Exp *right = ntest_exp->GetRightOperand();
        Type *stride_type = ntest_exp->GetStrideType();

        BinopKind base_kind = ntest_exp->GetBinopKind();
        if (NegativePhase())
          base_kind = NegateCompareBinop(base_kind);

        if (IsCompareBinop(base_kind)) {
          BinopKind reverse_kind = ReverseBinop(base_kind);
          VisitCompare(exp, base_kind, left, right, stride_type);
          VisitCompare(exp, reverse_kind, right, left, stride_type);
          continue;
        }
      }

      // treat as comparison with zero, either equal or notequal.
      Exp *zero = Exp::MakeInt(0);

      BinopKind base_kind = B_NotEqual;
      if (NegativePhase())
        base_kind = B_Equal;

      Type *type = test_exp->GetType();
      if (type)
        base_kind = PointerBinop(base_kind);

      VisitCompare(exp, base_kind, test_exp, zero, type);
    }
  }
};

void GetBaseCompares(BlockMemory *mcfg, Bit *bit,
                     Vector<BaseCompare> *compares,
                     bool ignore_disjunction)
{
  HasExitVisitor exit_visitor;
  bit->DoVisit(&exit_visitor, true);

  if (!exit_visitor.has_exit) {
    BaseCompareVisitor visitor(mcfg, compares, ignore_disjunction);
    bit->DoVisit(&visitor, true);
  }
}

// visitor to get implicit comparisons from certain binary operations.
class ExtraCompareVisitor : public ExpVisitor
{
 public:
  Vector<BaseCompare> *compares;

  ExtraCompareVisitor(Vector<BaseCompare> *_compares)
    : ExpVisitor(VISK_All), compares(_compares)
  {}

  void Visit(Exp *exp)
  {
    if (ExpBinop *nexp = exp->IfBinop()) {
      // just run the base compare visitor over any side constraint
      // generated by the solver for this binop.

      Vector<Bit*> bits;
      GetBinopConstraints(nexp, &bits, false);

      for (size_t ind = 0; ind < bits.Size(); ind++) {
        Bit *bit = bits[ind];
        BaseCompareVisitor visitor(NULL, compares, false);
        bit->DoVisit(&visitor, true);
      }
    }
  }
};

void GetExtraCompares(Bit *bit, Vector<BaseCompare> *compares)
{
  ExtraCompareVisitor visitor(compares);
  bit->DoVisit(&visitor, true);
}

void GetBaseAssigns(BlockMemory *mcfg, Vector<BaseAssign> *assigns)
{
  BlockCFG *cfg = mcfg->GetCFG();

  for (PPoint point = 1; point <= cfg->GetPointCount(); point++) {
    const Vector<GuardAssign> *alist = mcfg->GetAssigns(point);

    if (alist) {
      for (size_t aind = 0; aind < alist->Size(); aind++) {
        const GuardAssign &gts = alist->At(aind);
        assigns->PushBack(BaseAssign(gts.left, gts.right));
      }
    }
  }
}

// visitor for filtering out comparisons we aren't interested in
// the equalities from.
class CompareEqualityVisitor : public ExpVisitor
{
public:
  bool exclude;
  CompareEqualityVisitor()
    : ExpVisitor(VISK_All), exclude(false)
  {}

  void Visit(Exp *exp)
  {
    if (exp->IsClobber())
      exclude = true;
  }
};

void GetCompareEqualities(const Vector<BaseCompare> &compares,
                          Vector<BaseCompare> *equality_compares)
{
  for (size_t ind = 0; ind < compares.Size(); ind++) {
    const BaseCompare &cmp = compares[ind];

    CompareEqualityVisitor visitor;
    cmp.target->DoVisit(&visitor);

    if (visitor.exclude)
      continue;

    // whether we are going to increment and/or decrement the target
    // to get the new expression being compared with.
    bool do_incr = false;
    bool do_decr = false;

    switch (cmp.kind) {

    case B_LessThan:
    case B_LessThanP:
      do_decr = true;
      break;

    case B_GreaterThan:
    case B_GreaterThanP:
      do_incr = true;
      break;

    case B_NotEqual:
    case B_NotEqualP:
      do_incr = true;
      do_decr = true;
      break;

    default:
      break;
    }

    if (do_incr) {
      Exp *one = Exp::MakeInt(1);
      BinopKind incr_kind = (cmp.stride_type ? B_PlusPI : B_Plus);
      BinopKind cmp_kind = (cmp.stride_type ? B_GreaterEqualP : B_GreaterEqual);

      Exp *incr_target =
        Exp::MakeBinop(incr_kind, cmp.target, one, cmp.stride_type);

      AddCompare(equality_compares, cmp.test,
                 cmp_kind, cmp.source, incr_target, cmp.stride_type);
    }

    if (do_decr) {
      Exp *one = Exp::MakeInt(1);
      BinopKind decr_kind = (cmp.stride_type ? B_MinusPI : B_Minus);
      BinopKind cmp_kind = (cmp.stride_type ? B_LessEqualP : B_LessEqual);

      Exp *decr_target =
        Exp::MakeBinop(decr_kind, cmp.target, one, cmp.stride_type);

      AddCompare(equality_compares, cmp.test,
                 cmp_kind, cmp.source, decr_target, cmp.stride_type);
    }

    if (!do_incr && !do_decr) {
      AddCompare(equality_compares, cmp.test,
                 cmp.kind, cmp.source, cmp.target, cmp.stride_type);
    }
  }
}

/////////////////////////////////////////////////////////////////////
// invariant inference
/////////////////////////////////////////////////////////////////////

// it is possible that lval changes by delta with each iteration
// of the analyzed loop.
struct BaseDelta
{
  Exp *lval;

  // delta is zero for variable length or unknown deltas.
  int delta;

  // optional stride type for pointer increments/decrements.
  Type *stride_type;

  // the change in lval has been found to be monotonic. (lval does not
  // necessarily change by delta with each iteration though).
  bool monotonic_incr;
  bool monotonic_decr;

  BaseDelta()
    : lval(NULL), delta(0), stride_type(NULL),
      monotonic_incr(false), monotonic_decr(false)
  {}

  BaseDelta(Exp *_lval, int _delta, Type *_stride_type)
    : lval(_lval), delta(_delta), stride_type(_stride_type),
      monotonic_incr(false), monotonic_decr(false)
  {}
};

// intermediate data computed for invariant inference.
struct InvariantState
{
  // list of possible deltas for terms in this loop.
  Vector<BaseDelta> deltas;

  // list of terminator comparisons within this loop.
  Vector<TerminatorInfo> terminators;

  // list of comparisons made within this loop. these are comparisons
  // required for the recursive loop invocation to be reachable.
  Vector<BaseCompare> compares;

  // list of assignments made within this loop. for 't := s',
  // there will be a 't ~ s' assignment.
  Vector<BaseAssign> assigns;

  void Print(BlockId *id)
  {
    logout << "INVARIANT: State: " << id << endl;

    for (size_t ind = 0; ind < deltas.Size(); ind++) {
      const BaseDelta &d = deltas[ind];
      logout << "  delta " << d.lval << ": " << d.delta;
      if (d.stride_type)
        logout << " (" << d.stride_type << ")";
      logout << endl;
    }

    for (size_t ind = 0; ind < terminators.Size(); ind++) {
      const TerminatorInfo &term = terminators[ind];
      logout << "  terminator " << term.target << ": "
             << term.terminate_test << " ~ " << term.terminate_int << endl;
    }

    for (size_t ind = 0; ind < compares.Size(); ind++) {
      const BaseCompare &cmp = compares[ind];
      logout << "  compare " << cmp.source
             << " " << BinopString(cmp.kind) << " " << cmp.target << endl;
    }

    for (size_t ind = 0; ind < assigns.Size(); ind++) {
      const BaseAssign &asn = assigns[ind];
      logout << "  assign " << asn.left
             << " := " << asn.right << endl;
    }
  }
};

void FillDeltas(BlockMemory *mcfg, InvariantState *state)
{
  PPoint exit_point = mcfg->GetCFG()->GetExitPoint();
  Assert(exit_point);

  BlockModset *mod = GetBlockModset(mcfg->GetId());

  for (size_t ind = 0; ind < mod->GetModsetCount(); ind++) {
    const PointValue &v = mod->GetModsetLval(ind);
    if (v.kind)
      continue;

    Exp *lval = v.lval;

    // get the element type for pointer lvalues.
    Type *type = NULL;

    if (Type *base_type = lval->GetType()) {
      if (TypePointer *nbase = base_type->IfPointer())
        type = nbase->GetTargetType();
    }

    GuardExpVector values;
    mcfg->GetValComplete(lval, NULL, exit_point, &values, true);

    for (size_t ind = 0; ind < values.Size(); ind++) {
      const GuardExp &gs = values[ind];

      // incorporate this guard into the state's compares.
      GetBaseCompares(mcfg, gs.guard, &state->compares);

      // check for *t +/- n, for integer inc/dec.
      if (ExpBinop *nexp = gs.exp->IfBinop()) {
        BinopKind binop_kind = nexp->GetBinopKind();

        long value;
        Exp *nonconst = nexp->HasConstant(&value);

        if (nonconst && ExpDereference(nonconst) == lval) {
          int delta = 0;

          if (binop_kind == B_Plus)
            delta = (int) value;
          else if (binop_kind == B_Minus)
            delta = - (int) value;

          if (delta) {
            state->deltas.PushBack(BaseDelta(lval, delta, NULL));
            continue;
          }
        }
      }

      // check for index{*t,+/-n}, for pointer inc/dec.
      if (ExpIndex *nexp = gs.exp->IfIndex()) {
        if (ExpInt *index = nexp->GetIndex()->IfInt()) {
          long delta;
          if (index->GetInt(&delta)) {
            if (type && ExpDereference(nexp->GetTarget()) == lval) {
              state->deltas.PushBack(BaseDelta(lval, delta, type));
              continue;
            }
          }
        }
      }

      // otherwise leave a delta of zero.
      state->deltas.PushBack(BaseDelta(lval, 0, type));
    }
  }
};

// get an expression for the value of the lvalue at initial entry
// to the loop being tested.
Exp* GetInitialValue(InvariantTester *tester, Exp *lval)
{
  if (tester->parent_tests.Size() == 1) {
    const LoopInvariantPoint &parent_test = tester->parent_tests[0];

    const Vector<GuardExp> &entry_values =
      parent_test.mcfg->GetVal(lval, NULL, parent_test.point);

    // use the parent values directly if all the following conditions hold:
    // - there is just a single value.
    // - the value does not change over iterations of the loop,
    //   nor by the parent itself.
    // - the value can be expanded in the caller of the loop parent
    //   (this filters out ExpVal expressions).
    // - the value has one or fewer terms (constant or simple lvalue).

    if (entry_values.Size() == 1) {
      Exp *single_val = entry_values[0].exp;

      if (UseCallerExp(single_val, false) && single_val->TermCount() <= 1) {
        if (tester->exit_test.mcfg->IsExpPreserved(single_val) &&
            parent_test.mcfg->IsExpPreserved(single_val)) {
          return single_val;
        }
      }
    }
  }

  // use ExpInitial to make an expression for the value outside the loop.
  return Exp::MakeInitial(lval, NULL);
}

// get an expression for (first - second) * delta.
// consumes references on first and second,
// but not stride_type (if stride_type is specified).
Exp* GetScaledDifference(Exp *first, Exp *second,
                         Type *stride_type, int delta)
{
  BinopKind binop = B_Minus;
  if (stride_type)
    binop = B_MinusPP;

  Exp *diff;
  if (delta > 0) {
    diff = Exp::MakeBinop(binop, first, second, stride_type);
  }
  else if (delta < 0) {
    diff = Exp::MakeBinop(binop, second, first, stride_type);
  }
  else {
    // can't have a delta of zero.
    Assert(false);
  }

  if (delta < 0)
    delta = -delta;

  if (delta == 1) {
    // don't need to do any scaling.
    return diff;
  }
  else {
    Exp *delta_exp = Exp::MakeInt(delta);
    return Exp::MakeBinop(B_Mult, diff, delta_exp);
  }
}

// is lval incremented by the specified delta with each iteration?
// if so returns the stride type of that increment and the initial value
// at loop entry.
bool IsPointerIncremented(InvariantTester *tester, const InvariantState &state,
                          const BaseDelta &delta,
                          Exp *lval, Type **stride_type, Exp **init_value)
{
  Assert(delta.monotonic_incr);

  if (delta.stride_type) {
    // regular pointer increment: x++ with each iteration.
    if (ExpDereference(lval) == delta.lval) {
      *stride_type = delta.stride_type;
      *init_value = GetInitialValue(tester, delta.lval);
      return true;
    }
  }
  else {
    // index increment: x[i]; i++ with each iteration.
    if (ExpIndex *nlval = lval->IfIndex()) {
      Exp *target = nlval->GetTarget();
      Exp *index = nlval->GetIndex();
      if (ExpDereference(index) == delta.lval) {
        *stride_type = nlval->GetElementType();

        Exp *init_index = GetInitialValue(tester, delta.lval);
        *init_value = Exp::MakeIndex(target, *stride_type, init_index);
        return true;
      }
    }
  }

  return false;
}

void InferLoopInvariants(InvariantTester *tester, InvariantState &state)
{
  // look for monotonic changes in terms. val >= loop_entry(val) for
  // incremented values, val <= loop_entry(val) for decremented values.

  for (size_t ind = 0; ind < state.deltas.Size(); ind++) {
    BaseDelta &d = state.deltas[ind];

    bool test_le = (d.delta <= 0);
    bool test_ge = (d.delta >= 0);

    Exp *drf_lval = Exp::MakeDrf(d.lval);
    Exp *init_lval = GetInitialValue(tester, d.lval);

    if (test_le) {
      BinopKind binop = d.stride_type ? B_LessEqualP : B_LessEqual;
      Bit *compare_test =
        Exp::MakeCompareBit(binop, drf_lval, init_lval, d.stride_type);
      if (tester->AddCandidateInvariant(compare_test))
        d.monotonic_decr = true;
    }

    if (test_ge) {
      BinopKind binop = d.stride_type ? B_GreaterEqualP : B_GreaterEqual;
      Bit *compare_test =
        Exp::MakeCompareBit(binop, drf_lval, init_lval, d.stride_type);
      if (tester->AddCandidateInvariant(compare_test))
        d.monotonic_incr = true;
    }
  }

  // look for tests on terms which have deltas. if val is incremented,
  // guess 'val <= oval' if there is a 'val != oval' or 'val < oval',
  // similarly if val is decremented.

  for (size_t xind = 0; xind < state.deltas.Size(); xind++) {
    const BaseDelta &d = state.deltas[xind];
    if (d.delta == 0)
      continue;

    for (size_t cind = 0; cind < state.compares.Size(); cind++) {
      const BaseCompare &cmp = state.compares[cind];

      if (ExpDereference(cmp.source) != d.lval)
        continue;

      BinopKind old_binop = NonPointerBinop(cmp.kind);

      if (old_binop != B_NotEqual &&
          old_binop != (d.delta > 0 ? B_LessThan : B_GreaterThan))
        continue;

      BinopKind binop = (d.delta < 0) ? B_GreaterEqual : B_LessEqual;
      if (d.stride_type)
        binop = PointerBinop(binop);

      Exp *drf_lval = Exp::MakeDrf(d.lval);

      Bit *compare_test =
        Exp::MakeCompareBit(binop, drf_lval, cmp.target, d.stride_type);

      if (tester->AddCandidateInvariant(compare_test)) {
        // success!
      }
      else {
        // try an implication: 'loop_entry(val) <= oval => val <= oval'
        Exp *init_lval = GetInitialValue(tester, d.lval);

        Bit *init_test =
          Exp::MakeCompareBit(binop, init_lval, cmp.target, d.stride_type);

        Bit *imply_test = Bit::MakeImply(init_test, compare_test);
        tester->AddCandidateInvariant(imply_test);
      }
    }
  }

  // look for values which are both tested for and assigned somewhere within
  // the loop. if there is an 'val cmp oval' and 'nval := val', guess
  // '*nval cmp oval'.

  for (size_t aind = 0; aind < state.assigns.Size(); aind++) {
    const BaseAssign &assign = state.assigns[aind];

    if (!assign.right->IsLvalue())
      continue;

    for (size_t cind = 0; cind < state.compares.Size(); cind++) {
      const BaseCompare &cmp = state.compares[cind];

      if (assign.right != cmp.source)
        continue;

      Exp *drf_left = Exp::MakeDrf(assign.left);
      Bit *compare_test =
        Exp::MakeCompareBit(cmp.kind, drf_left, cmp.target, cmp.stride_type);

      if (tester->AddCandidateInvariant(compare_test)) {
        // success!
      }
      else {
        Exp *init_left = GetInitialValue(tester, assign.left);

        Bit *init_test =
          Exp::MakeCompareBit(cmp.kind, init_left, cmp.target, cmp.stride_type);

        Bit *imply_test = Bit::MakeImply(init_test, compare_test);
        tester->AddCandidateInvariant(imply_test);
      }
    }
  }

  // look for flags indicating the loop ran. if there is a 'val cmp n0'
  // and a 'val := n1' (n0 != n1), then for all modified terms
  // guess 'term != loop_entry(term) ==> loop_entry(val) != n0 || val != n0'

  for (size_t aind = 0; aind < state.assigns.Size(); aind++) {
    const BaseAssign &assign = state.assigns[aind];

    if (!assign.right->IsInt())
      continue;

    for (size_t cind = 0; cind < state.compares.Size(); cind++) {
      const BaseCompare &cmp = state.compares[cind];

      if (ExpDereference(cmp.source) != assign.left)
        continue;
      if (!cmp.target->IsInt())
        continue;
      if (cmp.kind != B_Equal && cmp.kind != B_NotEqual)
        continue;
      if (cmp.target == assign.right)
        continue;

      for (size_t dind = 0; dind < state.deltas.Size(); dind++) {
        const BaseDelta &d = state.deltas[dind];

        Exp *drf_term = Exp::MakeDrf(d.lval);
        Exp *init_term = GetInitialValue(tester, d.lval);
        BinopKind diff_binop = d.stride_type ? B_NotEqualP : B_NotEqual;
        Bit *diff_cmp =
          Exp::MakeCompareBit(diff_binop, drf_term, init_term, d.stride_type);

        Exp *init_val = GetInitialValue(tester, assign.left);
        Bit *init_cmp =
          Exp::MakeCompareBit(B_NotEqual, init_val, cmp.target);

        Bit *after_cmp =
          Exp::MakeCompareBit(B_NotEqual, cmp.source, cmp.target);

        Bit *both_cmp = Bit::MakeOr(init_cmp, after_cmp);
        Bit *imply_test = Bit::MakeImply(diff_cmp, both_cmp);
        tester->AddCandidateInvariant(imply_test);
      }
    }
  }

  // look for linear relationships between terms by checking each of the
  // possible deltas pairwise against one another.

  for (size_t xind = 0; xind < state.deltas.Size(); xind++) {
    for (size_t yind = 0; yind < xind; yind++) {
      const BaseDelta &xd = state.deltas[xind];
      const BaseDelta &yd = state.deltas[yind];

      if (xd.lval == yd.lval)
        continue;

      if (xd.delta == 0 || yd.delta == 0)
        continue;

      // get the deref values of x and y.
      Exp *drf_x = Exp::MakeDrf(xd.lval);
      Exp *drf_y = Exp::MakeDrf(yd.lval);

      // get the base values of x and y at initial loop entry.
      Exp *init_x = GetInitialValue(tester, xd.lval);
      Exp *init_y = GetInitialValue(tester, yd.lval);

      // if we expect that x changes by xdelta each iteration,
      // and y changes by ydelta each iteration, then this
      // expression should be a loop invariant:
      // (x - xinit) / xdelta == (y - yinit) / ydelta
      // or equivalently:
      // (x - xinit) * ydelta == (y - yinit) * xdelta

      // compute the scaled difference between the deref and base values of
      // x and y.
      Exp *diff_x = GetScaledDifference(drf_x, init_x,
                                        xd.stride_type, yd.delta);
      Exp *diff_y = GetScaledDifference(drf_y, init_y,
                                        yd.stride_type, xd.delta);

      // add the equality as a candidate invariant.
      Bit *equal_test =
        Exp::MakeCompareBit(B_Equal, diff_x, diff_y, NULL);
      if (tester->AddCandidateInvariant(equal_test)) {
        // success!
      }
      else {
        // weaken the invariant; try '<=' and '>=' instead of '=='.
        Bit *le_test =
          Exp::MakeCompareBit(B_LessEqual, diff_x, diff_y, NULL);
        if (tester->AddCandidateInvariant(le_test)) {
          // success!
        }
        else {
          Bit *ge_test =
            Exp::MakeCompareBit(B_GreaterEqual, diff_x, diff_y, NULL);
          tester->AddCandidateInvariant(ge_test);
        }
      }
    }
  }

  // look for terminator checks by finding terms compared with some constant
  // which have a constant delta of one in each iteration.

  for (size_t dind = 0; dind < state.deltas.Size(); dind++) {
    const BaseDelta &delta = state.deltas[dind];

    if (!delta.monotonic_incr)
      continue;

    // whether we found any candidate terminator invariant.
    bool found_test = false;

    for (size_t zind = 0; zind < state.terminators.Size(); zind++) {
      const TerminatorInfo &info = state.terminators[zind];

      Type *stride_type;
      Exp *init_target;

      if (IsPointerIncremented(tester, state, delta, info.target,
                               &stride_type, &init_target)) {
        Bit *test = GetTerminatorInvariant(stride_type,
                                           info.target, init_target,
                                           info.terminate_test,
                                           info.terminate_int);
        if (test)
          tester->AddCandidateInvariant(test);

        found_test = true;
      }
    }

    if (!found_test) {
      // last ditch attempt to find a terminator test. if this is a pointer
      // which may be incremented a variable amount, guess a zero terminator.
      Exp *target = Exp::MakeDrf(delta.lval);

      if (Type *stride_type = target->GetType()) {
        Exp *init_target = GetInitialValue(tester, delta.lval);
        Exp *terminate_test = Exp::MakeEmpty();
        ExpInt *terminate_int = Exp::MakeInt(0);

        Bit *test = GetTerminatorInvariant(stride_type, target, init_target,
                                           terminate_test, terminate_int);
        if (test)
          tester->AddCandidateInvariant(test);
      }
    }
  }
}

void InferFunctionInvariants(InvariantTester *tester,
                             const InvariantState &state)
{
  for (size_t aind = 0; aind < state.assigns.Size(); aind++) {
    const BaseAssign &assign = state.assigns[aind];

    // only looking at return assignments for now.
    if (!assign.left->IsVar())
      continue;
    if (assign.left->AsVar()->GetVariable()->Kind() != VK_Return)
      continue;

    Exp *exit_left = Exp::MakeExit(assign.left, NULL);

    // skip any coercions on the right side.
    Exp *assign_right = assign.right;
    if (ExpUnop *nassign_right = assign_right->IfUnop()) {
      if (nassign_right->GetUnopKind() == U_Coerce)
        assign_right = nassign_right->GetOperand();
    }

    // same checks for comparisons against assignment results as for loops.

    if (assign_right->IsLvalue()) {
      for (size_t cind = 0; cind < state.compares.Size(); cind++) {
        const BaseCompare &cmp = state.compares[cind];

        if (assign_right == cmp.source) {
          Bit *compare_test =
            Exp::MakeCompareBit(cmp.kind, exit_left, cmp.target, cmp.stride_type);
          tester->AddCandidateInvariant(compare_test);
        }
      }
    }

    if (ExpBinop *nright = assign_right->IfBinop()) {
      BinopKind binop = nright->GetBinopKind();
      Exp *left = nright->GetLeftOperand();
      Exp *right = nright->GetRightOperand();

      // if the right side is 'x + y', try 'rval >= x' and 'rval >= y'.

      if (binop == B_Plus) {
        Bit *compare_left =
          Exp::MakeCompareBit(B_GreaterEqual, exit_left, left);
        tester->AddCandidateInvariant(compare_left);

        Bit *compare_right =
          Exp::MakeCompareBit(B_GreaterEqual, exit_left, right);
        tester->AddCandidateInvariant(compare_right);
      }

      // if the right side is 'x - y', try 'rval >= 0'.

      if (binop == B_Minus || binop == B_MinusPP) {
        Exp *zero = Exp::MakeInt(0);
        Bit *compare_test =
          Exp::MakeCompareBit(B_GreaterEqual, exit_left, zero);
        tester->AddCandidateInvariant(compare_test);
      }
    }
  }
}

/////////////////////////////////////////////////////////////////////
// invariant inference
/////////////////////////////////////////////////////////////////////

void InferInvariants(BlockSummary *sum, const Vector<Exp*> &arithmetic_list)
{
  InvariantTester tester(sum);
  InvariantState state;

  for (size_t ind = 0; ind < tester.assumed_bits.Size(); ind++) {
    Bit *bit = tester.assumed_bits[ind];
    GetBaseCompares(sum->GetMemory(), bit, &state.compares);
  }

  // get term deltas only when inferring loop invariants.
  if (sum->GetId()->Kind() == B_Loop)
    FillDeltas(sum->GetMemory(), &state);

  InferTerminatorTests(sum, arithmetic_list, &state.terminators);
  GetBaseAssigns(sum->GetMemory(), &state.assigns);

  if (print_invariants.IsSpecified())
    state.Print(sum->GetId());

  if (sum->GetId()->Kind() == B_Loop)
    InferLoopInvariants(&tester, state);
  else if (sum->GetId()->Kind() == B_Function)
    InferFunctionInvariants(&tester, state);
}

NAMESPACE_XGILL_END
