
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

#include "sufficient.h"

#include <infer/invariant.h>
#include <infer/expand.h>

NAMESPACE_XGILL_BEGIN

// limit to use when generating possible equalities for an expression.
#define EQUALITY_LIMIT 100

/////////////////////////////////////////////////////////////////////
// sufficient conditions utility
/////////////////////////////////////////////////////////////////////

ConfigOption checker_sufficient(CK_String, "ck-sufficient", "",
    "print the specified sufficient tests [all: all sufficient]");

// structure to manage testing of potential sufficient conditions.
struct SufficientTester
{
  CheckerState *state;
  CheckerFrame *frame;
  CheckerPropagate *propagate;

  bool verbose;

  // receives propagations for each sufficient condition found.
  Vector<CheckerPropagate*> *propagate_list;

  SufficientTester(CheckerPropagate *_propagate,
                   Vector<CheckerPropagate*> *_propagate_list)
    : state(_propagate->m_frame->State()),
      frame(_propagate->m_frame), propagate(_propagate), verbose(false),
      propagate_list(_propagate_list)
  {
    char buf[40];
    sprintf(buf, "%zd", propagate->m_id);

    if (checker_sufficient.IsSpecified() &&
        (strcmp(checker_sufficient.StringValue(), "all") == 0 ||
         strcmp(checker_sufficient.StringValue(), buf) == 0))
      verbose = true;
  }

  // returns true if bit is a useful condition for testing as sufficient
  // (no loop-modified terms, preserves reachability of assert, etc.)
  // regardless of whether it is actually sufficient.
  bool TestBit(Bit *bit)
  {
    Vector<Bit*> &tested_list = propagate->m_sufficient_tested_list;
    Vector<Bit*> &possible_list = propagate->m_sufficient_possible_list;
    Vector<Bit*> &sufficient_list = propagate->m_sufficient_list;

    Solver *solver = state->GetSolver();

    if (tested_list.Contains(bit)) {
      if (possible_list.Contains(bit))
        return true;
      return false;
    }

    if (verbose)
      logout << "SUFFICIENT: " << frame
             << ": Testing " << bit << " [" << bit->Hash() << "]" << endl;

    tested_list.PushBack(bit);

    // don't test for sufficient conditions if a timeout has occurred.
    if (TimerAlarm::ActiveExpired()) {
      if (verbose)
        logout << "SUFFICIENT: " << frame << ": Alarm expired" << endl;
      return false;
    }

    // check that the sufficient condition does not render the point
    // of the assertion unreachable: the solver is still satisfiable after
    // asserting the sufficient condition. this also takes care of
    // unsatisfiable sufficient conditions.

    state->PushContext();

    // ignore bits we can't do any propagation from.

    CheckerPropagate *test_propagate =
      new CheckerPropagate(frame, propagate->m_point,
                           propagate->m_allow_point);
    test_propagate->SetTest(bit);

    // propagations can trigger new solver side conditions. TODO: should figure
    // out what's going on here.
    if (!solver->IsSatisfiable()) {
      state->PopContext();
      return false;
    }

    if (test_propagate->m_where->IsNone()) {
      if (verbose)
        logout << "SUFFICIENT: " << frame << ": Failed propagate: "
               << test_propagate->m_where << endl;
      state->PopContext();
      delete test_propagate;
      return false;
    }

    // assert the tested sufficient holds in the frame.
    frame->AddAssert(bit);

    if (!solver->IsSatisfiable()) {
      // the sufficient condition rendered the assertion point unreachable.
      if (verbose)
        logout << "SUFFICIENT: " << frame
               << ": Renders point unreachable" << endl;

      state->PopContext();
      delete test_propagate;
      return false;
    }

    // this is a good potential sufficient condition, remember it.
    possible_list.PushBack(bit);

    // check whether the bit is actually a sufficient condition.
    // just assert the original negated safe bit, and if it is unsatisfiable
    // it cannot occur under this sufficient condition.

    state->AssertBaseBits();

    bool satisfiable = solver->IsSatisfiable();

    if (verbose) {
      if (satisfiable) {
        logout << "SUFFICIENT: " << frame
               << ": Not a sufficient condition:" << endl;
        solver->PinAssign();
        solver->PrintRawAssignment();
        solver->UnpinAssign();
      }
      else {
        logout << "SUFFICIENT: " << frame << ": Success!" << endl;
      }
    }

    if (!satisfiable) {
      sufficient_list.PushBack(bit);
      propagate_list->PushBack(test_propagate);
    }
    else {
      delete test_propagate;
    }

    state->PopContext();
    return true;
  }
};

/////////////////////////////////////////////////////////////////////
// implication based sufficient conditions
/////////////////////////////////////////////////////////////////////

void GetImplySufficient(CheckerFrame *frame, Vector<Bit*> *imply_list)
{
  // only getting implications for loops for now.
  if (frame->Kind() != B_Loop)
    return;

  // look for assumed bits of the form 'A || B'.
  // then check if either !A or !B is a sufficient condition
  // (this will force the other half of the implication to hold).

  for (size_t bind = 0; bind < frame->m_assumed_bits.Size(); bind++) {
    Bit *bit = frame->m_assumed_bits[bind];

    if (bit->Kind() == BIT_Or) {
      for (size_t oind = 0; oind < bit->GetOperandCount(); oind++) {
        Bit *op = bit->GetOperand(oind);
        Bit *nop = Bit::MakeNot(op);

        if (!imply_list->Contains(nop))
          imply_list->PushBack(nop);
      }
    }
  }
}

/////////////////////////////////////////////////////////////////////
// equality based sufficient conditions
/////////////////////////////////////////////////////////////////////

Exp* MatchEquality(Exp *base, const BaseCompare &equality)
{
  Exp *source = equality.source;
  Exp *target = equality.target;

  // check for the source and base being the same value.
  if (source == base)
    return target;

  // check for the source and base begin different bounds on the same lvalue.
  if (source->IsBound() && base->IsBound()) {
    ExpBound *nsource = source->AsBound();
    ExpBound *nbase = base->AsBound();

    if (nsource->GetTarget() != nbase->GetTarget())
      return NULL;
    if (nsource->GetBoundKind() != nbase->GetBoundKind())
      return NULL;

    size_t base_width = nbase->GetStrideType()->Width();
    size_t source_width = nsource->GetStrideType()->Width();

    if (source_width == base_width)
      return target;

    // only handling upper bounds where the base's width is an even multiple
    // of the source's width. this is to handle cases where there is an
    // equality due to calling a primitive allocation function.
    if (nbase->GetBoundKind() != BND_Upper)
      return NULL;
    if (source_width == 0)
      return NULL;
    if (base_width < source_width)
      return NULL;

    size_t factor = base_width / source_width;
    if (source_width * factor != base_width)
      return NULL;

    // construct a new equality and recurse on it. the base's bound
    // can be compared with (target / factor).
    Exp *factor_exp = Exp::MakeInt(factor);
    return Exp::MakeBinop(B_Div, target, factor_exp);
  }

  return NULL;
}

class EqualityMapper : public ExpMultiMapper
{
 public:
  BlockMemory *mcfg;
  bool verbose;

  const Vector<BaseCompare> &equalities;
  Vector<Exp*> &expand_stack;

  EqualityMapper(BlockMemory *_mcfg, bool _verbose,
                 const Vector<BaseCompare> &_equalities,
                 Vector<Exp*> &_expand_stack)
    : ExpMultiMapper(VISK_All, EQUALITY_LIMIT), mcfg(_mcfg), verbose(_verbose),
      equalities(_equalities), expand_stack(_expand_stack)
  {}

  void MultiMap(Exp *exp, Vector<Exp*> *res)
  {
    // follow possible equalities for lvalues and non-arithmetic binops
    // appearing in the input formula.
    bool handle_exp = false;

    if (exp->IsLvalue() || exp->IsBound() || exp->IsTerminate())
      handle_exp = true;
    else if (ExpBinop *nexp = exp->IfBinop()) {
      switch (nexp->GetBinopKind()) {
      case B_Mod:
      case B_BitwiseAnd:
      case B_BitwiseOr:
      case B_BitwiseXOr:
      case B_Min:
      case B_Max:
        handle_exp = true;
      default:
        break;
      }
    }

    /*
    // special cased constant substitution. if we see an 'n < val'
    // or 'n+1 <= val' and a comparison 'n+1 ~ oval', try substituting
    // 'oval <= val'.

    if (ExpBinop *nexp = exp->IfBinop()) {
      long left_value, right_value;
      BinopKind kind = nexp->GetBinopKind();
      Exp *left = nexp->GetLeftOperand();
      Exp *right = nexp->GetRightOperand();

      if ((kind == B_LessThan || kind == B_LessEqual) &&
          left->IsInt() && left->AsInt()->GetInt(&left_value)) {
        for (size_t ind = 0; ind < equalities.Size(); ind++) {
          const BaseCompare &equality = equalities[ind];
          if (equality.target->IsInt() &&
              equality.target->AsInt()->GetInt(&right_value) &&
              right_value == left_value + (kind == B_LessThan ? 1 : 0)) {
            Exp *new_exp = Exp::MakeBinop(B_LessEqual, equality.source, right);
            ExpAddResult(new_exp, res);
          }
        }
      }
    }
    */

    if (!handle_exp) {
      ExpAddResult(exp, res);
      return;
    }

    bool is_loop = (mcfg->GetId()->Kind() == B_Loop);

    // for loops, only follow equalities for terms which change with
    // each iteration.
    if (is_loop && mcfg->IsExpPreserved(exp)) {
      ExpAddResult(exp, res);
      return;
    }

    ExpAddResult(exp, res);

    // try to substitute the expression for anything it might share
    // an ==/<=/>= relationship with.

    for (size_t ind = 0; ind < equalities.Size(); ind++) {
      const BaseCompare &equality = equalities[ind];

      // watch for recursion when following compares.
      if (expand_stack.Contains(equality.test))
        continue;

      // check if there is a match between the exp and equality source.
      Exp *new_target = MatchEquality(exp, equality);

      if (new_target) {
        // keep track of the tests we use during recursive mapping.
        expand_stack.PushBack(equality.test);

        // list to hold result of mapping this substitution.
        Vector<Exp*> sub_res;

        EqualityMapper sub_mapper(mcfg, verbose, equalities, expand_stack);
        new_target->DoMultiMap(&sub_mapper, &sub_res);

        expand_stack.PopBack();

        // for functions, filter out substitutions which resulted in an
        // increase in the number of leaf terms in the expression. this both
        // gets rid of results we don't care about and prevents exponential
        // blowup. we don't need to worry about this for loops because
        // we only follow substitutions for values which change in each
        // iteration, a similar (and less crude) filtering.
        size_t base_term_count = exp->TermCount();

        if (verbose)
          logout << "SUFFICIENT: Substituted: " << exp
                 << " [" << sub_res.Size() << "]" << endl;

        for (size_t rind = 0; rind < sub_res.Size(); rind++) {
          Exp *res_exp = sub_res[rind];

          if (is_loop || res_exp->TermCount() <= base_term_count) {
            if (verbose)
              logout << "  Added: " << res_exp << endl;
            ExpAddResult(res_exp, res);
          }
          else {
            if (verbose)
              logout << "  Dropped: " << res_exp << endl;
          }
        }
      }
    }
  }
};

// if exp is a subtraction (exp0 - exp1) and exp1 is an lvalue, return exp1.
static inline Exp* GetSubtractedExp(Exp *exp)
{
  ExpBinop *nexp = exp->IfBinop();
  if (!nexp)
    return NULL;
  BinopKind kind = nexp->GetBinopKind();
  if (kind != B_Minus && kind != B_MinusPP)
    return NULL;
  Exp *right = nexp->GetRightOperand();
  if (right->IsLvalue())
    return right;
  return NULL;
}

// bit0 and bit1 are plain comparisons which establish an upper and lower
// bound on the same term. bit0 is from a candidate sufficient condition,
// bit1 is from an assumption on the contained frame.
bool BitShareOperands(Bit *bit0, Bit *bit1)
{
  Exp *exp0 = bit0->GetVar();
  Exp *exp1 = bit1->GetVar();

  if (!exp0 || !exp1)
    return false;

  ExpBinop *nexp0 = exp0->IfBinop();
  ExpBinop *nexp1 = exp1->IfBinop();

  if (!nexp0 || !nexp1)
    return false;

  BinopKind kind0 = NonPointerBinop(nexp0->GetBinopKind());
  BinopKind kind1 = NonPointerBinop(nexp1->GetBinopKind());

  // both bits must be < or <= (> and >= are simplified away).
  if (kind0 != B_LessThan && kind0 != B_LessEqual)
    return false;
  if (kind1 != B_LessThan && kind1 != B_LessEqual)
    return false;

  Exp *left0 = nexp0->GetLeftOperand();
  Exp *left1 = nexp1->GetLeftOperand();

  Exp *right0 = nexp0->GetRightOperand();
  Exp *right1 = nexp1->GetRightOperand();

  // check for a pointer bound and its target on the same sides of the binops.
  // (the bound can only appear in bit0, which came from a sufficient cond).

  // bound(A) <= *, A <= *
  if (ExpBound *nleft0 = left0->IfBound()) {
    if (nleft0->GetTarget() == left1)
      return true;
  }

  // * <= bound(A), * <= A
  if (ExpBound *nright0 = right0->IfBound()) {
    if (nright0->GetTarget() == right1)
      return true;
  }

  // check the exact term being on opposite sides of the binops.

  // A <= *, * <= A
  if (left0->IsLvalue() && left0 == right1)
    return true;

  // * <= A, A <= *
  if (right0->IsLvalue() && right0 == left1)
    return true;

  // check the term being on both sides of the binop, in opposite phases.

  Exp *negleft0 = GetSubtractedExp(left0);
  Exp *negleft1 = GetSubtractedExp(left1);

  Exp *negright0 = GetSubtractedExp(right0);
  Exp *negright1 = GetSubtractedExp(right1);

  // * - A <= *, A <= *
  // * <= * - A, * <= A
  if (negleft0 == left1 || negright0 == right1)
    return true;

  // A <= *, * - A <= *
  // * <= A, * <= * - A
  if (left0 == negleft1 || right0 == negright1)
    return true;

  return false;
}

void GetEqualitySufficient(SufficientTester *tester, Bit *safe_bit,
                           const Vector<Bit*> &imply_list)
{
  CheckerFrame *frame = tester->frame;

  Vector<BaseCompare> compares;
  Vector<BaseCompare> equalities;

  // populate comparisons from assumptions the error is contingent on.

  for (size_t ind = 0; ind < frame->m_assumed_extra.Size(); ind++) {
    Bit *bit = frame->m_assumed_extra[ind];
    GetBaseCompares(frame->Memory(), bit, &compares, true);
  }

  for (size_t ind = 0; ind < frame->m_assumed_bits.Size(); ind++) {
    Bit *bit = frame->m_assumed_bits[ind];

    // reduced by the assumed_extra bits to narrow any disjunctions
    // to the paths we are actually taking.
    for (size_t xind = 0; xind < frame->m_assumed_extra.Size(); xind++)
      bit = Bit::ReduceBit(bit, frame->m_assumed_extra[xind]);

    GetBaseCompares(frame->Memory(), bit, &compares, true);
  }

  // get compares from nonlinear and other operations in the safe bit.
  GetExtraCompares(safe_bit, &compares);

  // get the equalities implied by the base comparisons.
  GetCompareEqualities(compares, &equalities);

  if (tester->verbose) {
    for (size_t ind = 0; ind < equalities.Size(); ind++) {
      const BaseCompare &cmp = equalities[ind];
      logout << "EQUALITY: " << cmp.source << " ~ " << cmp.target << endl;
    }
  }

  Vector<Exp*> expand_stack;
  EqualityMapper mapper(frame->Memory(), tester->verbose,
                        equalities, expand_stack);

  // try to propagate equalities to remove loop-local data from the test.
  Vector<Bit*> equality_res;
  safe_bit->DoMultiMap(&mapper, &equality_res);

  for (size_t ind = 0; ind < equality_res.Size(); ind++) {
    Bit *bit = equality_res[ind];
    bool possible = tester->TestBit(bit);

    // see if there is an assume we could combine this bit with. if there is
    // an equality test 'a <= b' and an assumed bit 'c <= a || ...',
    // test 'a <= b && c <= a'. this is designed to catch the compound
    // sufficient conditions we need when a '!=' operator is used in the
    // code, e.g. 'len <= length(buf) && 0 <= len'

    if (possible) {
      for (size_t bind = 0; bind < imply_list.Size(); bind++) {
        Bit *op = imply_list[bind];

        if (BitShareOperands(bit, op)) {
          Bit *combine = Bit::MakeAnd(bit, op);
          tester->TestBit(combine);
        }
      }
    }
  }
}

/////////////////////////////////////////////////////////////////////
// sufficient condition inference
/////////////////////////////////////////////////////////////////////

void GetSufficientConditions(CheckerPropagate *propagate, Bit *safe_bit,
                             Vector<CheckerPropagate*> *propagate_list)
{
  CheckerState *state = propagate->m_frame->State();
  Solver *solver = state->GetSolver();

  if (!solver->IsSatisfiable())
    return;

  SufficientTester tester(propagate, propagate_list);

  if (tester.verbose)
    logout << "SUFFICIENT: " << propagate->m_frame
           << ": Finding candidates: " << safe_bit << endl;

  // get any potential sufficient conditions from the frame's impliciations.
  Vector<Bit*> imply_list;
  GetImplySufficient(propagate->m_frame, &imply_list);

  // try to follow possible equalities to get a sufficient condition.
  GetEqualitySufficient(&tester, safe_bit, imply_list);

  for (size_t ind = 0; ind < imply_list.Size(); ind++)
    tester.TestBit(imply_list[ind]);

  // try to mark the bit itself as a sufficient condition.
  tester.TestBit(safe_bit);
}

NAMESPACE_XGILL_END
