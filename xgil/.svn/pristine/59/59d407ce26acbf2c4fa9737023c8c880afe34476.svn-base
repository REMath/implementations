
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

#include "infer.h"

#include "expand.h"
#include "nullterm.h"
#include "invariant.h"

#include <imlang/storage.h>
#include <imlang/loopsplit.h>
#include <memory/baked.h>
#include <memory/escape.h>
#include <memory/mstorage.h>
#include <solve/solver.h>

// cutoff for arithmetic escape propagation.
#define ARITHMETIC_ESCAPE_LIMIT 50

NAMESPACE_XGILL_BEGIN

// escape structure for identifying accesses which use pointer arithmetic.
// TODO: there are two big holes in how we identify these writes currently:
// 1. only considering arithmetic within the current function. the following
//    code will slip by:
//    int* foo() { return &buf[n]; }
//    void main() { int *x = foo(); *x = 0; }
// 2. bad treatment of buffers of structures. the following code will slip by:
//    void main() { str *s = &buf[n]; s->f = 0; }
//    void main() { str *s = &buf[n]; int *x = &s->f; *x = 0; }
// these issues really need to get fixed.
class ArithmeticEscape : public EscapeStatus
{
 public:
  Variable *m_function;
  Vector<Exp*> &m_arithmetic_lvals;

  ArithmeticEscape(Variable *function,
                   Vector<Exp*> &arithmetic_lvals)
    : EscapeStatus(true, ARITHMETIC_ESCAPE_LIMIT),
      m_function(function), m_arithmetic_lvals(arithmetic_lvals)
  {}

  Trace* Visit(Trace *trace, bool *skip_cutoff)
  {
    if (trace->Kind() != TK_Func)
      return NULL;

    if (trace->GetFunction() != m_function)
      return NULL;

    // add the trace's lvalue to each of the summaries.
    Exp *exp = trace->GetValue();

    if (!m_arithmetic_lvals.Contains(exp))
      m_arithmetic_lvals.PushBack(exp);
    return trace;
  }
};

// if the specified assignment involves pointer arithmetic on the right side,
// propagate that arithmetic to the left side and everything it might flow to.
void ProcessArithmeticAssign(ArithmeticEscape *escape, BlockId *id,
                             Exp *left, Exp *right)
{
  // the expression has to be an ExpIndex for it to be arithmetic.
  // this is the result of operations like 'p++' if p is a pointer.
  if (right->IsIndex()) {

    // get the expression we will be running escape propagation on.
    // this is the deref of the left side of the assignment.
    Exp *left_drf = Exp::MakeDrf(left);

    if (Trace *trace = Trace::MakeFromExp(id, left_drf)) {
      bool success = escape->FollowEscape(trace);

      if (!success) {
        logout << "WARNING: ProcessArithmeticAssign: "
               << "escape propagation failed" << endl;
      }
    }
  }
}

// visitor for adding assertions at each buffer access. for now buffer
// assertion generation is crude and only looks for ExpIndex and ExpDrf
// expressions whose value is ever that of the result of pointer arithmetic
// (according to any assignments in the function's CFGs).
class BufferScanVisitor : public ExpVisitor
{
 public:
  Vector<AssertInfo> &asserts;
  const Vector<Exp*> &arithmetic_list;
  PPoint point;
  bool check_writes;

  BufferScanVisitor(Vector<AssertInfo> &_asserts,
                    const Vector<Exp*> &_arithmetic_list,
                    PPoint _point, bool _check_writes)
    : ExpVisitor(VISK_Lval),
      asserts(_asserts), arithmetic_list(_arithmetic_list),
      point(_point), check_writes(_check_writes)
  {}

  void Visit(Exp *lval)
  {
    // buffer which is being accessed.
    Exp *base = NULL;

    // element type of the buffer.
    Type *elem_type = NULL;

    // index of the buffer being accessed.
    Exp *index = NULL;

    // peel off any leading fields.
    while (ExpFld *nlval = lval->IfFld())
      lval = nlval->GetTarget();

    if (ExpIndex *nlval = lval->IfIndex()) {
      base = nlval->GetTarget();
      elem_type = nlval->GetElementType();
      index = nlval->GetIndex();

      if (base->IsIndex()) {
        // multidimensional array access, the base needs to be checked
        // if we are looking for reads.
        if (!check_writes)
          Visit(base);
      }
    }

    if (ExpDrf *nlval = lval->IfDrf()) {
      // see if this expression is in the values we know might be the result
      // of pointer arithmetic.
      bool is_arithmetic = false;

      if (Exp *new_lval = Trace::SanitizeExp(lval))
        is_arithmetic = arithmetic_list.Contains(new_lval);

      if (is_arithmetic) {
        base = lval;

        elem_type = nlval->GetType();
        if (!elem_type) {
          // TODO: need better handling for this case. *((int*)n)
          elem_type = Type::MakeVoid();
        }

        index = Exp::MakeInt(0);
      }
    }

    if (base || elem_type || index) {
      Assert(base && elem_type && index);

      AssertInfo lower_info;
      AssertInfo upper_info;

      lower_info.kind = check_writes ? ASK_WriteUnderflow : ASK_ReadUnderflow;
      upper_info.kind = check_writes ? ASK_WriteOverflow : ASK_ReadOverflow;

      lower_info.cls = ASC_Check;
      upper_info.cls = ASC_Check;

      lower_info.point = point;
      upper_info.point = point;

      Exp *lbound = Exp::MakeBound(BND_Lower, base, elem_type);
      lower_info.bit = Exp::MakeCompareBit(B_GreaterEqual, index, lbound);

      Exp *ubound = Exp::MakeBound(BND_Upper, base, elem_type);
      upper_info.bit = Exp::MakeCompareBit(B_LessThan, index, ubound);

      // if we are looking for reads, only add if there is not already
      // an equivalent write (we add writes to the assert list first).
      // this will obscure the reads in statements like '(*p)++', oh well.

      bool skip_lower = false;
      bool skip_upper = false;

      // don't restrict just to reads here, so that this works as a general
      // purpose dupe-remover.
      for (size_t ind = 0; ind < asserts.Size(); ind++) {
        const AssertInfo &info = asserts[ind];
        if (info.point == point && info.bit == lower_info.bit)
          skip_lower = true;
        if (info.point == point && info.bit == upper_info.bit)
          skip_upper = true;
      }

      if (!skip_lower)
        asserts.PushBack(lower_info);

      if (!skip_upper)
        asserts.PushBack(upper_info);
    }
  }
};

// visitor for adding assertions at each integer operation which
// might overflow.
class IntegerScanVisitor : public ExpVisitor
{
 public:
  Vector<AssertInfo> &asserts;
  PPoint point;

  IntegerScanVisitor(Vector<AssertInfo> &_asserts, PPoint _point)
    : ExpVisitor(VISK_All), asserts(_asserts), point(_point)
  {}

  void Visit(Exp *exp)
  {
    size_t bits = exp->Bits();
    bool sign = exp->Sign();

    if (!bits)
      return;

    Assert(exp->IsUnop() || exp->IsBinop());

    AssertInfo lower_info;
    AssertInfo upper_info;

    lower_info.kind = ASK_IntegerUnderflow;
    upper_info.kind = ASK_IntegerOverflow;

    lower_info.cls = ASC_Check;
    upper_info.cls = ASC_Check;

    lower_info.point = point;
    upper_info.point = point;

    const char *min_value = GetMinimumInteger(bits, sign);
    const char *max_value = GetMaximumInteger(bits, sign);

    Exp *min_exp = Exp::MakeIntStr(min_value);
    Exp *max_exp = Exp::MakeIntStr(max_value);

    lower_info.bit = Exp::MakeCompareBit(B_GreaterEqual, exp, min_exp);
    upper_info.bit = Exp::MakeCompareBit(B_LessEqual, exp, max_exp);

    asserts.PushBack(lower_info);
    asserts.PushBack(upper_info);
  }
};

// visitor for adding assertions at each access on a type whose
// contents or value may be affected by GC.
class GCScanVisitor : public ExpVisitor
{
 public:
  Vector<AssertInfo> &asserts;
  PPoint point;

  GCScanVisitor(Vector<AssertInfo> &_asserts, PPoint _point)
    : ExpVisitor(VISK_All),
      asserts(_asserts), point(_point)
  {}

  void Visit(Exp *lval)
  {
    // match any access which uses a GC thing type as an rvalue,
    // including those where the thing is not actually dereferenced.
    // we are watching not just for direct accesses to the thing,
    // but to places where it is copied to arguments, a return value,
    // a variable or heap location. any use of an GC thing pointer
    // not protected against GC is considered to be an error, and adding
    // these asserts aggressively lets us discharge reports easier and
    // generate reports close to the site of the actual problem.

    if (!lval->IsDrf())
      return;
    ExpDrf *nlval = lval->AsDrf();

    Type *type = nlval->GetType();
    if (type && type->IsCSU() && TypeIsGCThing(type->AsCSU())) {
      AssertInfo info;
      info.kind = ASK_GCSafe;
      info.cls = ASC_Check;
      info.point = point;

      Exp *target = nlval->GetTarget();
      if (target->IsFld() &&
          BlockSummary::FieldIsGCSafe(target->AsFld()->GetField())) {
        info.bit = Bit::MakeConstant(true);
      } else {
        Exp *gcsafe = Exp::MakeGCSafe(nlval->GetTarget(), false);
        info.bit = Bit::MakeVar(gcsafe);
      }

      asserts.PushBack(info);
    }
  }
};

// mark the trivial/redundant assertions in the specified list.
void MarkRedundantAssertions(BlockMemory *mcfg, Vector<AssertInfo> &asserts)
{
  BlockCFG *cfg = mcfg->GetCFG();

  // assertions are marked redundant in two passes:
  // 1. for each path reaching the assertion, the validity of the assertion is
  //    implied by one or more prior or future assertions.
  //    this pass also picks up assertions which trivially hold, where the
  //    assertion is valid due to the conditions along the paths themselves.
  // 2. there is an isomorphic assertion within an inner loop. it is
  //    sufficient to check just the inner assertion.

  // implication works differently for invariants vs. other assertions,
  // since the invariant condition will be asserted at block exit.

  // for regular assertions, an bit is redundant if (guard ==> bit)
  // is implied by the (oguard ==> obit) for other assertions:

  // VALID((oguard ==> obit) ==> (guard ==> bit))
  // !SAT(!((oguard ==> obit) ==> (guard ==> bit)))
  // !SAT(!(!(oguard ==> obit) || (guard ==> bit)))
  // !SAT((oguard ==> obit) && !(guard ==> bit))
  // !SAT((oguard ==> obit) && !(!guard || bit))
  // !SAT((oguard ==> obit) && guard && !bit)

  // for invariants, a bit is redundant if guard implies the oguard
  // for other invariants with the same asserted bit:

  // VALID(guard ==> oguard)
  // !SAT(!(guard ==> oguard))
  // !SAT(!(!guard || oguard))
  // !SAT(guard && !oguard)

  Solver *solver = new Solver("redundant");

  for (size_t ind = 0; ind < asserts.Size(); ind++) {
    AssertInfo &info = asserts[ind];
    solver->PushContext();

    Assert(info.cls == ASC_Check);

    // assert guard.
    Bit *guard = mcfg->GetGuard(info.point);
    solver->AddAssert(0, guard);

    if (info.kind != ASK_Invariant) {
      // assert !bit.
      Bit *not_bit = Bit::MakeNot(info.bit);

      Bit *result_not_bit;
      mcfg->TranslateBit(TRK_Point, info.point, not_bit, &result_not_bit);
      solver->AddAssert(0, result_not_bit);
    }

    if (!solver->IsSatisfiable()) {
      // the assert is tautological or is proved by the guard, thus trivial.
      info.cls = ASC_Trivial;
      solver->PopContext();
      continue;
    }

    // assert the remaining assertions in the summary hold.
    for (size_t aind = 0; aind < asserts.Size(); aind++) {
      const AssertInfo &oinfo = asserts[aind];

      // skip this assertion itself.
      if (info.point == oinfo.point && info.bit == oinfo.bit)
        continue;

      // skip assertions already marked as trivial or redundant.
      if (oinfo.cls != ASC_Check)
        continue;

      // skip assertions for a different kind than the original.
      // this avoids interference between the different kinds of assertions,
      // though it is unlikely to affect whether we actually mark an
      // assert as redundant.
      if (oinfo.kind != info.kind)
        continue;

      Bit *oguard = mcfg->GetGuard(oinfo.point);

      if (info.kind == ASK_Invariant) {
        // only compare with other invariants for the same bit.
        if (oinfo.bit != info.bit)
          continue;

        // assert !oguard
        Bit *not_oguard = Bit::MakeNot(oguard);
        solver->AddAssert(0, not_oguard);
      }
      else {
        // assert (oguard ==> obit).
        Bit *result_obit;
        mcfg->TranslateBit(TRK_Point, oinfo.point, oinfo.bit, &result_obit);

        Bit *imply_bit = Bit::MakeImply(oguard, result_obit);
        solver->AddAssert(0, imply_bit);
      }
    }

    if (!solver->IsSatisfiable()) {
      // the assert is implied by the remaining assertions, thus redundant.
      info.cls = ASC_Redundant;
    }

    solver->PopContext();
  }

  solver->Clear();
  delete solver;

  for (size_t ind = 0; ind < cfg->GetEdgeCount(); ind++) {
    PEdgeLoop *loop_edge = cfg->GetEdge(ind)->IfLoop();
    if (!loop_edge)
      continue;

    for (size_t aind = 0; aind < asserts.Size(); aind++) {
      AssertInfo &info = asserts[aind];

      if (info.cls != ASC_Check)
        continue;

      if (cfg->IsLoopIsomorphic(info.point)) {
        // this assertion's point is isomorphic to a point within the
        // loop body, so there will be an equivalent loop assertion.
        info.cls = ASC_Redundant;
      }
    }
  }
}

void InferSummaries(const Vector<BlockSummary*> &summary_list)
{
  static BaseTimer infer_timer("infer_summaries");
  Timer _timer(&infer_timer);

  if (summary_list.Empty())
    return;

  Variable *function = summary_list[0]->GetId()->BaseVar();
  Vector<BlockCFG*> *annot_list = BodyAnnotCache.Lookup(function->GetName());

  // all traces which might refer to the result of pointer arithmetic.
  Vector<Exp*> arithmetic_list;
  ArithmeticEscape escape(function, arithmetic_list);

  // initial pass over the CFGs to get traces used in pointer arithmetic.
  for (size_t ind = 0; ind < summary_list.Size(); ind++) {
    BlockSummary *sum = summary_list[ind];

    BlockCFG *cfg = sum->GetMemory()->GetCFG();
    for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
      PEdge *edge = cfg->GetEdge(eind);

      if (PEdgeAssign *assign_edge = edge->IfAssign()) {
        Exp *left = assign_edge->GetLeftSide();
        Exp *right = assign_edge->GetRightSide();
        ProcessArithmeticAssign(&escape, cfg->GetId(), left, right);
      }
    }
  }

  for (size_t ind = 0; ind < summary_list.Size(); ind++) {
    BlockSummary *sum = summary_list[ind];
    BlockMemory *mcfg = sum->GetMemory();
    BlockCFG *cfg = mcfg->GetCFG();

    // accumulate all the assertions at points in the CFG.
    Vector<AssertInfo> asserts;

    // add assertions at function exit for any postconditions.
    if (cfg->GetId()->Kind() == B_Function) {
      for (size_t aind = 0; annot_list && aind < annot_list->Size(); aind++) {
        BlockCFG *annot_cfg = annot_list->At(aind);

        if (annot_cfg->GetAnnotationKind() != AK_Postcondition)
          continue;
        if (Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg)) {
          AssertInfo info;
          info.kind = ASK_Annotation;
          info.cls = ASC_Check;
          info.point = cfg->GetExitPoint();
          info.bit = bit;
          asserts.PushBack(info);
        }
      }
    }

    // add assertions for any point annotations within the CFG.
    for (size_t pind = 0; pind < cfg->GetPointAnnotationCount(); pind++) {
      PointAnnotation pann = cfg->GetPointAnnotation(pind);
      BlockCFG *annot_cfg = GetAnnotationCFG(pann.annot);
      if (!annot_cfg) continue;

      if (annot_cfg->GetAnnotationKind() != AK_Assert)
        continue;

      if (Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg)) {
        AssertInfo info;
        info.kind = ASK_Annotation;
        info.cls = ASC_Check;
        info.point = pann.point;
        info.bit = bit;
        asserts.PushBack(info);
      }
    }

    for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
      PEdge *edge = cfg->GetEdge(eind);
      PPoint point = edge->GetSource();

      if (PEdgeAnnotation *nedge = edge->IfAnnotation()) {
        // add an assertion for this annotation if it not an assume.
        BlockCFG *annot_cfg = GetAnnotationCFG(nedge->GetAnnotationId());
        if (!annot_cfg) continue;

        if (annot_cfg->GetAnnotationKind() != AK_Assert &&
            annot_cfg->GetAnnotationKind() != AK_AssertRuntime) {
          continue;
        }

        if (Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg)) {
          AssertInfo info;
          info.kind = (annot_cfg->GetAnnotationKind() == AK_Assert)
            ? ASK_Annotation : ASK_AnnotationRuntime;
          info.cls = ASC_Check;
          info.point = point;
          info.bit = bit;
          asserts.PushBack(info);
        }
      }

      // add assertions for any invariants affected by a write.

      Exp *left = NULL;
      if (PEdgeAssign *nedge = edge->IfAssign())
        left = nedge->GetLeftSide();
      if (PEdgeCall *nedge = edge->IfCall())
        left = nedge->GetReturnValue();

      // for now our detection of affected invariants is pretty crude;
      // writes to fields can affect type invariants on the field's type
      // which use that field, and writes to global variables can affect
      // invariants on that global. TODO: pin this down once we draw a
      // precise line between which invariants can and can't be checked.

      if (left && left->IsFld()) {
        ExpFld *nleft = left->AsFld();
        String *csu_name = nleft->GetField()->GetCSUType()->GetCSUName();
        Vector<BlockCFG*> *comp_annot_list = CompAnnotCache.Lookup(csu_name);

        for (size_t aind = 0; comp_annot_list &&
                              aind < comp_annot_list->Size(); aind++) {
          BlockCFG *annot_cfg = comp_annot_list->At(aind);

          if (annot_cfg->GetAnnotationKind() != AK_Invariant)
            continue;
          Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg);
          if (!bit) continue;

          Vector<Exp*> lval_list;
          LvalListVisitor visitor(&lval_list);
          bit->DoVisit(&visitor);

          bool uses_field = false;
          for (size_t ind = 0; ind < lval_list.Size(); ind++) {
            if (ExpFld *lval = lval_list[ind]->IfFld()) {
              if (lval->GetField() == nleft->GetField())
                uses_field = true;
            }
          }

          if (uses_field) {
            // this is a type invariant which uses the field being written
            // as an lvalue. we need to assert this write preserves
            // the invariant.
            BlockId *id = annot_cfg->GetId();
            Variable *this_var = Variable::Make(id, VK_This, NULL, 0, NULL);
            Exp *this_exp = Exp::MakeVar(this_var);
            Exp *this_drf = Exp::MakeDrf(this_exp);

            Bit *new_bit = BitReplaceExp(bit, this_drf, nleft->GetTarget());

            AssertInfo info;
            info.kind = ASK_Invariant;
            info.cls = ASC_Check;
            info.point = point;
            info.bit = new_bit;
            asserts.PushBack(info);
          }
        }

        CompAnnotCache.Release(csu_name);
      }

      if (left && left->IsVar()) {
        Variable *var = left->AsVar()->GetVariable();
        if (var->Kind() == VK_Glob) {
          Vector<BlockCFG*> *glob_annot_list =
            InitAnnotCache.Lookup(var->GetName());

          for (size_t aind = 0; glob_annot_list &&
                                aind < glob_annot_list->Size(); aind++) {
            BlockCFG *annot_cfg = glob_annot_list->At(aind);

            Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg);
            if (!bit) continue;

            AssertInfo info;
            info.kind = ASK_Invariant;
            info.cls = ASC_Check;
            info.point = point;
            info.bit = bit;
            asserts.PushBack(info);
          }

          InitAnnotCache.Release(var->GetName());
        }
      }

      if (PEdgeCall *nedge = edge->IfCall()) {
        // add assertions for any callee preconditions.

        // pull preconditions from both direct and indirect calls.
        Vector<Variable*> callee_names;

        if (Variable *callee = nedge->GetDirectFunction()) {
          callee_names.PushBack(callee);
        }
        else {
          CallEdgeSet *callees = CalleeCache.Lookup(function);

          if (callees) {
            for (size_t cind = 0; cind < callees->GetEdgeCount(); cind++) {
              const CallEdge &edge = callees->GetEdge(cind);
              if (edge.where.id == cfg->GetId() && edge.where.point == point)
                callee_names.PushBack(edge.callee);
            }
          }

          // CalleeCache release is below.
        }

        for (size_t cind = 0; cind < callee_names.Size(); cind++) {
          String *callee = callee_names[cind]->GetName();
          Vector<BlockCFG*> *call_annot_list = BodyAnnotCache.Lookup(callee);

          for (size_t aind = 0;
               call_annot_list && aind < call_annot_list->Size(); aind++) {
            BlockCFG *annot_cfg = call_annot_list->At(aind);

            if (annot_cfg->GetAnnotationKind() != AK_Precondition)
              continue;
            if (Bit *bit = BlockMemory::GetAnnotationBit(annot_cfg)) {
              ConvertCallsiteMapper mapper(cfg, point, false);
              Bit *caller_bit = bit->DoMap(&mapper);
              if (!caller_bit)
                continue;

              AssertInfo info;
              info.kind = ASK_Annotation;
              info.cls = ASC_Check;
              info.point = point;
              info.bit = caller_bit;
              asserts.PushBack(info);
            }
          }

          BodyAnnotCache.Release(callee);
        }

        if (!nedge->GetDirectFunction())
          CalleeCache.Release(function);
      }

      BufferScanVisitor write_visitor(asserts, arithmetic_list, point, true);
      BufferScanVisitor read_visitor(asserts, arithmetic_list, point, false);
      IntegerScanVisitor integer_visitor(asserts, point);
      GCScanVisitor gcsafe_visitor(asserts, point);

      // only look at the written lvalues for the write visitor.
      if (PEdgeAssign *assign = edge->IfAssign())
        write_visitor.Visit(assign->GetLeftSide());
      if (PEdgeCall *call = edge->IfCall()) {
        if (Exp *returned = call->GetReturnValue())
          write_visitor.Visit(returned);
      }

      edge->DoVisit(&read_visitor);

      // disable integer overflow visitor for now.
      // edge->DoVisit(&integer_visitor);

      edge->DoVisit(&gcsafe_visitor);
    }

    if (cfg->GetId()->Kind() == B_Function) {
      BlockModset *modset = GetBlockModset(cfg->GetId());
      if (modset->CanGC()) {
        AssertInfo info;
        info.kind = ASK_CanGC;
        info.cls = ASC_Check;
        info.point = cfg->GetExitPoint();

        String *name = cfg->GetId()->BaseVar()->GetName();
        Variable *var = Variable::Make(NULL, VK_Glob, name, 0, name);
        Exp *varexp = Exp::MakeVar(var);
        Exp *gcsafe = Exp::MakeGCSafe(varexp, false);
        info.bit = Bit::MakeVar(gcsafe);
        asserts.PushBack(info);
      }
    }

    MarkRedundantAssertions(mcfg, asserts);

    // move the finished assertion list into the summary.
    for (size_t ind = 0; ind < asserts.Size(); ind++) {
      const AssertInfo &info = asserts[ind];
      sum->AddAssert(info.kind, info.cls, info.point, info.bit);
    }
  }

  // infer delta and termination invariants for all summaries.
  for (size_t ind = 0; ind < summary_list.Size(); ind++)
    InferInvariants(summary_list[ind], arithmetic_list);

  BodyAnnotCache.Release(function->GetName());
}

NAMESPACE_XGILL_END
