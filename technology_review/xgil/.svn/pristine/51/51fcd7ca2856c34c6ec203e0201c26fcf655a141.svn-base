
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

#include "frame.h"
#include "propagate.h"

#include <memory/baked.h>
#include <infer/expand.h>

NAMESPACE_XGILL_BEGIN

ConfigOption checker_fixup(CK_Flag, "ck-fixup", NULL,
                           "try to fixup nonlinear applications for reports");

ConfigOption checker_assign(CK_Flag, "ck-assigns", NULL,
                            "print satisfying assignments at each report");

ConfigOption checker_dump(CK_Flag, "ck-dump", NULL,
                          "print checker state at each report");

/////////////////////////////////////////////////////////////////////
// CheckerFrame
/////////////////////////////////////////////////////////////////////

CheckerFrame::CheckerFrame(CheckerState *state, FrameId id,
                           BlockCFG *cfg, BlockMemory *mcfg,
                           BlockSummary *summary)
  : m_state(state), m_id(id),
    m_cfg(cfg), m_mcfg(mcfg), m_summary(summary),
    m_kind(cfg->GetId()->Kind()), m_end_point(0),
    m_caller_frame(0), m_caller_equalities(false), m_loop_parent_frame(0),
    m_heap_predecessor_frame(0), m_heap_successor_frame(0),
    m_caller_expand("caller_expand"),
    m_loop_parent_expand("loop_parent_expand"),
    m_callee_heap_frame(0), m_caller_heap_frame(0),
    m_checked_assertions(false)
{}

CheckerFrame::~CheckerFrame()
{
  for (size_t ind = 0; ind < m_callee_expand.Size(); ind++)
    delete m_callee_expand[ind];
}

void CheckerFrame::Print()
{
  logout << "Frame " << m_id << " : " << m_summary->GetId() << endl;

  if (m_end_point)
    logout << "  end_point " << m_end_point << endl;

  if (m_caller.id)
    logout << "  caller " << m_caller << endl;

  if (m_caller_frame)
    logout << "  caller_frame " << m_caller_frame << endl;

  if (m_caller_equalities)
    logout << "  caller_equalities" << endl;

  if (m_loop_parent.id)
    logout << "  loop_parent " << m_loop_parent << endl;

  if (m_loop_parent_frame)
    logout << "  loop_parent_frame " << m_loop_parent_frame << endl;

  for (size_t ind = 0; ind < m_callee_frames.Size(); ind++) {
    PointFrameId point_id = m_callee_frames[ind];
    logout << "  callee " << point_id.id
         << " (point " << point_id.point << ")" << endl;
  }

  for (size_t ind = 0; ind < m_loop_tail_frames.Size(); ind++) {
    PointFrameId point_id = m_loop_tail_frames[ind];
    logout << "  loop_tail " << point_id.id
         << " (point " << point_id.point << ")" << endl;
  }

  for (size_t ind = 0; ind < m_loop_skip_points.Size(); ind++)
    logout << "  loop_skip " << m_loop_skip_points[ind] << endl;

  if (m_heap_predecessor_frame)
    logout << "  heap_predecessor " << m_heap_predecessor_frame << endl;

  if (m_heap_successor_frame)
    logout << "  heap_successor " << m_heap_successor_frame << endl;

  m_caller_expand.Print();
  m_loop_parent_expand.Print();

  for (size_t ind = 0; ind < m_callee_expand.Size(); ind++)
    m_callee_expand[ind]->Print();

  if (m_callee_heap_frame)
    logout << "  callee_heap_frame " << m_callee_heap_frame << endl;

  if (m_caller_heap_frame)
    logout << "  caller_heap_frame " << m_caller_heap_frame << endl;
}

CheckerFrame* CheckerFrame::GetCalleeFrame(PPoint point)
{
  for (size_t ind = 0; ind < m_callee_frames.Size(); ind++) {
    PointFrameId other_id = m_callee_frames[ind];
    if (other_id.point == point)
      return m_state->GetFrame(other_id.id);
  }
  return NULL;
}

CheckerFrame* CheckerFrame::GetLoopTailFrame(PPoint point)
{
  for (size_t ind = 0; ind < m_loop_tail_frames.Size(); ind++) {
    PointFrameId other_id = m_loop_tail_frames[ind];
    if(other_id.point == point)
      return m_state->GetFrame(other_id.id);
  }
  return NULL;
}

bool CheckerFrame::IsSkippedLoop(PPoint point)
{
  return m_loop_skip_points.Contains(point);
}

CheckerFrame* CheckerFrame::GetCallerFrame()
{
  return m_state->GetFrame(m_caller_frame);
}

CheckerFrame* CheckerFrame::GetLoopParentFrame()
{
  return m_state->GetFrame(m_loop_parent_frame);
}

CheckerFrame* CheckerFrame::GetHeapPredecessorFrame()
{
  return m_state->GetFrame(m_heap_predecessor_frame);
}

CheckerFrame* CheckerFrame::GetHeapSuccessorFrame()
{
  return m_state->GetFrame(m_heap_successor_frame);
}

CheckerFrame* CheckerFrame::GetCalleeHeapFrame()
{
  return m_state->GetFrame(m_callee_heap_frame);
}

// gets a pending expression from the specified set and adds it to the
// state's topmost context, or NULL if the set is empty.
static inline Exp* GetExpandPending(CheckerExpandSet *expand,
                                    CheckerFrame *frame)
{
  if (expand->pending.Empty())
    return NULL;

  Exp *exp = expand->pending.Back();
  expand->pending.PopBack();

  CheckerExpandItem item(frame->Id(), expand, exp);

  Vector<CheckerExpandItem> *context = frame->State()->TopContext();
  context->PushBack(item);

  return exp;
}

void CheckerFrame::ExpandPendingExps()
{
  Solver *solver = m_state->GetSolver();
  Assert(!solver->HasPendingExp());

  // frames which we will transitively need to expand pending exps on.
  Vector<CheckerFrame*> expand_frames;

  // try to expand a set within a caller. this could be either the caller
  // set or the loop parent set, but not both (the caller set contains
  // the loop parent set).

  CheckerFrame *caller_frame = NULL;
  CheckerExpandSet *caller_expand = NULL;
  PPoint caller_point = 0;

  if (m_caller_equalities) {
    caller_frame = GetCallerFrame();
    caller_expand = &m_caller_expand;
    caller_point = m_caller.point;
  }
  else if (m_loop_parent_frame) {
    caller_frame = GetLoopParentFrame();
    caller_expand = &m_loop_parent_expand;
    caller_point = m_loop_parent.point;
  }

  if (caller_frame && !caller_expand->pending.Empty()) {
    TranslateKind kind = caller_frame->CalleeTranslateKind(caller_point);
    BlockMemory *caller_mcfg = caller_frame->m_mcfg;

    while (Exp *exp = GetExpandPending(caller_expand, this)) {
      // get the corresponding caller values.
      GuardExpVector caller_list;
      caller_mcfg->TranslateExp(kind, caller_point, exp, &caller_list);

      for (size_t ind = 0; ind < caller_list.Size(); ind++) {
        const GuardExp &gs = caller_list[ind];
        solver->AddEquality(m_id, caller_frame->m_id,
                            exp, NULL, false,
                            gs.exp, gs.guard, true);
      }
    }

    caller_frame->MarkPendingExps();
    expand_frames.PushBack(caller_frame);
  }

  // add caller equalities for the function pointer if this frame was called
  // indirectly.

  if (m_kind == B_Function && caller_frame) {
    BlockMemory *caller_mcfg = caller_frame->m_mcfg;
    BlockCFG *caller_cfg = caller_mcfg->GetCFG();
    PEdge *edge = caller_cfg->GetSingleOutgoingEdge(caller_point);

    if (edge->IsCall() && edge->AsCall()->GetDirectFunction() == NULL) {
      // get the address of this function itself.
      Variable *var = m_mcfg->GetCFG()->GetId()->BaseVar();
      Exp *var_exp = Exp::MakeVar(var);

      // get the function expressions at the call site.
      GuardExpVector receiver_list;
      caller_mcfg->TranslateReceiver(caller_point, &receiver_list);

      for (size_t ind = 0; ind < receiver_list.Size(); ind++) {
        const GuardExp &gs = receiver_list[ind];
        solver->AddEquality(0, caller_frame->m_id,
                            var_exp, NULL, false,
                            gs.exp, gs.guard, true);
      }

      caller_frame->MarkPendingExps();
      expand_frames.PushBack(caller_frame);
    }
  }

  // add equalities for any skipped loops.

  for (size_t ind = 0; ind < m_callee_expand.Size(); ind++) {
    CheckerExpandSet *expand = m_callee_expand[ind];
    PPoint point = expand->point;

    if (expand->pending.Empty())
      continue;
    if (!IsSkippedLoop(point))
      continue;

    while (Exp *exp = GetExpandPending(expand, this)) {
      // get the values the expression might correspond to after the call.
      GuardExpVector after_values;
      m_mcfg->TranslateExp(TRK_Callee, point, exp, &after_values);

      for (size_t pind = 0; pind < after_values.Size(); pind++) {
        const GuardExp &after_gs = after_values[pind];

        // replace any clobbers with their value before the call. we only need
        // to worry about clobber side effects because loops cannot have
        // 'must' assignment side effects.

        GuardExpVector prev_values;
        m_mcfg->TranslateExp(TRK_SkipClobber, point,
                             after_gs.exp, &prev_values);

        for (size_t vind = 0; vind < prev_values.Size(); vind++) {
          const GuardExp &prev_gs = prev_values[vind];
          solver->AddEquality(m_id, m_id,
                              after_gs.exp, NULL, false,
                              prev_gs.exp, prev_gs.guard, true);
        }
      }
    }

    MarkPendingExps();
    expand_frames.PushBack(this);
  }

  // add equalities for any regular callees and loop tails.

  for (size_t ind = 0; ind < m_callee_expand.Size(); ind++) {
    CheckerExpandSet *expand = m_callee_expand[ind];
    PPoint point = expand->point;

    if (expand->pending.Empty())
      continue;

    CheckerFrame *callee_frame;
    if (m_mcfg->GetCFG()->PointEdgeIsCall(point))
      callee_frame = GetCalleeFrame(point);
    else
      callee_frame = GetLoopTailFrame(point);

    if (!callee_frame)
      continue;

    BlockMemory *callee_mcfg = callee_frame->m_mcfg;
    PPoint exit_point = callee_mcfg->GetCFG()->GetExitPoint();

    while (Exp *exp = GetExpandPending(expand, this)) {
      // get the values the expression might correspond to after the call.
      GuardExpVector caller_values;
      m_mcfg->TranslateExp(TRK_Callee, point, exp, &caller_values);

      // get the possible values the expression might have at callee exit.
      GuardExpVector callee_values;
      callee_mcfg->TranslateExp(TRK_Exit, exit_point,
                                exp, &callee_values);

      for (size_t pind = 0; pind < caller_values.Size(); pind++) {
        const GuardExp &caller_gs = caller_values[pind];

        for (size_t cind = 0; cind < callee_values.Size(); cind++) {
          const GuardExp &callee_gs = callee_values[cind];

          solver->AddEquality(callee_frame->m_id, m_id,
                              callee_gs.exp, callee_gs.guard, true,
                              caller_gs.exp, caller_gs.guard, false);
        }
      }
    }

    callee_frame->MarkPendingExps();
    expand_frames.PushBack(callee_frame);
  }

  // do any transitive expansion required by the expansions we performed.
  for (size_t ind = 0; ind < expand_frames.Size(); ind++)
    expand_frames[ind]->ExpandPendingExps();
}

void CheckerFrame::ConnectCallee(CheckerFrame *callee_frame, PPoint point,
                                 bool add_equalities)
{
  Assert(!callee_frame->m_caller_frame);
  Assert(!GetCalleeFrame(point));

  BlockId *caller = m_mcfg->GetId();

  callee_frame->m_caller = BlockPPoint(caller, point);
  callee_frame->m_caller_frame = m_id;
  callee_frame->m_caller_equalities = add_equalities;

  PointFrameId point_id(point, callee_frame->m_id);
  m_callee_frames.PushBack(point_id);
}

void CheckerFrame::ConnectLoopChild(CheckerFrame *child_frame, PPoint point)
{
  // for now this caller frame does not have a list of all its loop
  // iteration children, only the first (GetCallee) and last (GetLoopTail).

  BlockPPoint where(m_mcfg->GetId(), point);
  child_frame->m_loop_parent = where;
  child_frame->m_loop_parent_frame = m_id;
}

void CheckerFrame::ConnectLoopTail(CheckerFrame *tail_frame, PPoint point)
{
  // there shouldn't be callees of any sort at this point.
  Assert(!GetCalleeFrame(point));
  Assert(!GetLoopTailFrame(point));
  Assert(!tail_frame->m_loop_parent_frame);

  ConnectLoopChild(tail_frame, point);

  PointFrameId point_id(point, tail_frame->m_id);
  m_loop_tail_frames.PushBack(point_id);
}

void CheckerFrame::ConnectHeapRead(CheckerFrame *read_frame)
{
  Assert(!read_frame->m_heap_predecessor_frame);
  Assert(!m_heap_successor_frame);

  read_frame->m_heap_predecessor_frame = m_id;
  m_heap_successor_frame = read_frame->m_id;
}

void CheckerFrame::AddSkipLoop(PPoint point)
{
  Assert(!m_loop_skip_points.Contains(point));
  m_loop_skip_points.PushBack(point);
}

void CheckerFrame::SetCalleeHeapFrame(CheckerFrame *heap_frame)
{
  Assert(m_heap_predecessor_frame == 0);
  Assert(m_callee_heap_frame == 0);
  Assert(heap_frame->m_caller_heap_frame == 0);

  if (heap_frame != this) {
    m_callee_heap_frame = heap_frame->m_id;
    heap_frame->m_caller_heap_frame = m_id;
  }
}

void CheckerFrame::DisconnectCallee(CheckerFrame *callee_frame, PPoint point)
{
  Assert(callee_frame->m_caller_frame == m_id);
  Assert(callee_frame == GetCalleeFrame(point));

  callee_frame->m_caller = BlockPPoint();
  callee_frame->m_caller_frame = 0;
  callee_frame->m_caller_equalities = false;

  for (size_t ind = 0; ind < m_callee_frames.Size(); ind++) {
    PointFrameId id = m_callee_frames[ind];
    if (id.point == point) {
      m_callee_frames[ind] = m_callee_frames.Back();
      m_callee_frames.PopBack();
    }
  }
}

void CheckerFrame::DisconnectLoopChild(CheckerFrame *child_frame, PPoint point)
{
  Assert(child_frame->m_loop_parent_frame == m_id);

  child_frame->m_loop_parent_frame = 0;
  child_frame->m_loop_parent = BlockPPoint();
}

void CheckerFrame::DisconnectLoopTail(CheckerFrame *tail_frame, PPoint point)
{
  Assert(tail_frame->m_loop_parent_frame == m_id);
  Assert(tail_frame == GetLoopTailFrame(point));

  DisconnectLoopChild(tail_frame, point);
  
  for (size_t ind = 0; ind < m_loop_tail_frames.Size(); ind++) {
    PointFrameId id = m_loop_tail_frames[ind];
    if (id.point == point) {
      m_loop_tail_frames[ind] = m_loop_tail_frames.Back();
      m_loop_tail_frames.PopBack();
      break;
    }
  }
}

void CheckerFrame::DisconnectHeapRead(CheckerFrame *read_frame)
{
  Assert(m_heap_successor_frame == read_frame->m_id);
  Assert(read_frame->m_heap_predecessor_frame == m_id);

  read_frame->m_heap_predecessor_frame = 0;
  m_heap_successor_frame = 0;
}

void CheckerFrame::RemoveSkipLoop(PPoint point)
{
  for (size_t ind = 0; ind < m_loop_skip_points.Size(); ind++) {
    if (m_loop_skip_points[ind] == point) {
      m_loop_skip_points[ind] = m_loop_skip_points.Back();
      m_loop_skip_points.PopBack();
      return;
    }
  }

  Assert(false);
}

void CheckerFrame::UnsetCalleeHeapFrame()
{
  if (CheckerFrame *heap_frame = GetCalleeHeapFrame()) {
    m_callee_heap_frame = 0;
    heap_frame->m_caller_heap_frame = 0;
  }
}

void CheckerFrame::PushCallerLoopParent(CheckerFrame *caller_frame)
{
  Assert(m_caller_frame == caller_frame->m_id);

  // is the caller frame an unrolled iteration of the same loop?
  if (m_kind == B_Loop && m_mcfg == caller_frame->m_mcfg) {
    // we only unroll loop iterations from the tail to the head, so the caller
    // frame should not have any loop parent or other info set right now.
    // the caller frame inherits any loop parent from the callee.
    Assert(!caller_frame->m_loop_parent_frame);

    if (m_loop_parent_frame) {
      caller_frame->m_loop_parent_frame = m_loop_parent_frame;
      caller_frame->m_loop_parent = m_loop_parent;
    }
  }
  else if (m_loop_parent_frame) {
    // the only caller of a loop iteration frame can be an unrolled iteration
    // of the same loop or the loop parent.
    Assert(m_loop_parent_frame == caller_frame->m_id);
  }
}

void CheckerFrame::AddAssert(Bit *bit, bool side_conditions)
{
  if (bit->IsTrue())
    return;

  m_state->GetSolver()->AddAssert(m_id, bit, side_conditions);
  MarkPendingExps();
}

// get a list of all terms mentioned in the edge conditions, assignments
// or arguments of the specified block.
void GetMemoryLvalues(BlockMemory *mcfg, Vector<Exp*> *lvalue_list)
{
  LvalListVisitor visitor(lvalue_list);

  BlockCFG *cfg = mcfg->GetCFG();
  Assert(cfg);

  for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
    PEdge *edge = cfg->GetEdge(eind);
    if (Bit *bit = mcfg->GetEdgeCond(edge))
      bit->DoVisit(&visitor);
  }

  for (PPoint point = 1; point <= cfg->GetExitPoint(); point++) {
    const Vector<GuardAssign> *assigns = mcfg->GetAssigns(point);
    if (assigns) {
      for (size_t ind = 0; ind < assigns->Size(); ind++) {
        assigns->At(ind).left->DoVisit(&visitor);
        assigns->At(ind).right->DoVisit(&visitor);

        // the left side itself is an lvalue.
        visitor.Visit(assigns->At(ind).left);
      }
    }

    const Vector<GuardAssign> *arguments = mcfg->GetArguments(point);
    if (arguments) {
      for (size_t ind = 0; ind < arguments->Size(); ind++)
        arguments->At(ind).right->DoVisit(&visitor);
    }
  }
}

void CheckerFrame::AssertPointGuard(PPoint point, bool allow_point)
{
  Solver *solver = m_state->GetSolver();

  Assert(!m_end_point);
  Assert(point);
  m_end_point = point;

  // if allow_point is set then we can pull in assumptions at the point itself.
  PPoint assume_point = allow_point ? (point + 1) : point;

  // add any assumptions given to us by the summary/annots for the block.
  Vector<AssumeInfo> assume_list;
  BlockSummary::GetAssumedBits(m_mcfg, assume_point, &assume_list);

  for (size_t ind = 0; ind < assume_list.Size(); ind++) {
    const AssumeInfo &info = assume_list[ind];
    m_assumed_bits.PushBack(info.bit);

    // if the assume came from an annotation, add its terms to the UI display.
    if (info.annot)
      m_state->GetSolver()->GetBitTerms(m_id, info.bit, &m_annotated_terms);
  }

  // add assumption that paths go through the specified point.
  Bit *point_guard = m_mcfg->GetGuard(point);
  m_assumed_bits.PushBack(point_guard);

  // assert the generated assumptions.
  for (size_t ind = 0; ind < m_assumed_bits.Size(); ind++) {
    Bit *bit = m_assumed_bits[ind];
    AddAssert(bit);
  }

  // add assertions to ignore the functions we're ignoring.
  BlockCFG *cfg = m_mcfg->GetCFG();

  for (size_t ind = 0; ind < cfg->GetEdgeCount(); ind++) {
    if (PEdgeCall *edge = cfg->GetEdge(ind)->IfCall()) {
      if (Variable *callee = edge->GetDirectFunction()) {
        IgnoreFunctionKind kind = IgnoreFunction(callee);

        if (kind == IGNORE_UNREACHABLE) {
          Bit *guard = m_mcfg->GetGuard(edge->GetSource());
          Bit *not_guard = Bit::MakeNot(guard);

          solver->AddConstraint(m_id, not_guard);
        }
        else if (kind == IGNORE_RETURN_ZERO) {
          Exp *ret_exp = Exp::MakeVar(NULL, VK_Return, NULL, 0, NULL);
          Exp *ret_drf = Exp::MakeDrf(ret_exp);
          Bit *ret_nonzero = Exp::MakeNonZeroBit(ret_drf);
          Bit *ret_zero = Bit::MakeNot(ret_nonzero);

          Bit *post_bit;
          m_mcfg->TranslateBit(TRK_Callee, edge->GetSource(),
                               ret_zero, &post_bit);
          solver->AddConstraint(m_id, post_bit);
        }
      }
    }
  }

  // add assertions from any heap invariants we are considering.
  if (!m_state->m_invariant_list.Empty()) {
    Vector<Exp*> lvalue_list;
    GetMemoryLvalues(m_mcfg, &lvalue_list);

    for (size_t ind = 0; ind < lvalue_list.Size(); ind++) {
      Exp *lval = lvalue_list[ind];

      for (size_t iind = 0; iind < m_state->m_invariant_list.Size(); iind++) {
        WhereInvariant *invariant = m_state->m_invariant_list[iind];
        invariant->AssertRecursive(this, lval);
      }
    }
  }
}

void CheckerFrame::PushAssumedBit(Bit *guard)
{
  m_assumed_extra.PushBack(guard);

  // undoing this assert will be taken care of by PopContext().
  AddAssert(guard);
}

void CheckerFrame::PopAssumedBit()
{
  m_assumed_extra.PopBack();
}

void CheckerFrame::MarkPendingExps()
{
  // expand all the pending expressions in two stages: one for val exps
  // and one for everything else.
  Solver *solver = m_state->GetSolver();

  // terms which we've encountered that aren't val expressions.
  Vector<Exp*> post_list;

  bool found_val = true;
  while (found_val) {
    found_val = false;

    Vector<Exp*> pending_list;
    solver->GetPendingExps(m_id, &pending_list);

    // expand any val terms we found, and put other terms on the post list.
    for (size_t ind = 0; ind < pending_list.Size(); ind++) {
      Exp *exp = pending_list[ind];

      if (solver->ExpandVal(m_id, exp))
        found_val = true;
      else
        post_list.PushBack(exp);
    }
  }

  Assert(!solver->HasPendingExp());

  // add information for each non-val term we found.
  for (size_t ind = 0; ind < post_list.Size(); ind++) {
    Exp *exp = post_list[ind];

    if (UseCallerExp(exp, m_kind == B_Function)) {
      // mark the exp for expansion in callers to frame.
      if (m_caller_expand.AddExp(exp)) {
        if (m_kind == B_Loop && m_mcfg->IsExpPreserved(exp)) {
          // also mark the exp for expansion in loop parents.
          m_loop_parent_expand.AddExp(exp);
        }
      }
    }

    if (PPoint point = UseCalleeExp(exp)) {
      Exp *callee = TranslateCalleeExp(m_mcfg, point, exp, m_id);

      // mark the exp for expansion in the specified callee of this frame.
      bool found = false;
      for (size_t ind = 0; ind < m_callee_expand.Size(); ind++) {
        if (m_callee_expand[ind]->point == point) {
          m_callee_expand[ind]->AddExp(callee);
          found = true;
          break;
        }
      }

      if (!found) {
        CheckerExpandSet *callee_set =
          new CheckerExpandSet("callee_expand", point);
        callee_set->AddExp(callee);
        m_callee_expand.PushBack(callee_set);
      }
    }
  }
}

CheckerFrame* CheckerFrame::GetPathRoot(bool follow_heap_writes)
{
  if (follow_heap_writes) {
    CheckerFrame *callee_heap = GetCalleeHeapFrame();
    CheckerFrame *heap_frame = callee_heap ? callee_heap : this;

    CheckerFrame *predecessor = heap_frame->GetHeapPredecessorFrame();
    if (predecessor)
      return predecessor->GetPathRoot(follow_heap_writes);
  }

  CheckerFrame *caller = GetCallerFrame();
  if (caller)
    return caller->GetPathRoot(follow_heap_writes);

  return this;
}

/////////////////////////////////////////////////////////////////////
// CheckerState
/////////////////////////////////////////////////////////////////////

CheckerState::CheckerState(AssertKind assert_kind)
  : m_solver(NULL), m_assert_kind(assert_kind), m_report_kind(RK_None),
    m_propagate_count(0), m_delayed_propagate_heap(NULL), m_path(NULL),
    m_trait_unsat(false), m_trait_heap(false)
{
  m_solver = new Solver("checker");

  // empty entry for frame Id zero.
  m_frames.PushBack(NULL);

  // context to receive initial changes to the solver/exps.
  PushContext();
}

CheckerState::~CheckerState()
{
  m_solver->Clear();
  delete m_solver;

  // the propagations in m_stack are not owned by the state, they reside
  // on the program stack itself.

  for (size_t ind = 0; ind < m_invariant_list.Size(); ind++)
    delete m_invariant_list[ind];
  for (size_t ind = 0; ind < m_precondition_list.Size(); ind++)
    delete m_precondition_list[ind];

  for (size_t ind = 0; ind < m_frames.Size(); ind++) {
    if (m_frames[ind])
      delete m_frames[ind];
  }

  if (m_path)
    delete m_path;
}

// visitor to add trait information to a CheckerState based on terms
// mentioned in the safe/sufficient bits within the state.
class CheckerTraitVisitor : public ExpVisitor
{
 public:
  CheckerState *state;

  CheckerTraitVisitor(CheckerState *_state)
    : ExpVisitor(VISK_All), state(_state)
  {}

  void Visit(Exp *exp)
  {
    // add mentioned fields.
    if (ExpFld *nexp = exp->IfFld()) {
      Field *field = nexp->GetField();
      if (!state->m_trait_fields.Contains(field))
        state->m_trait_fields.PushBack(field);
    }

    // add mentioned stride types.
    if (ExpBound *nexp = exp->IfBound()) {
      Type *type = nexp->GetStrideType();
      if (!state->m_trait_bound_types.Contains(type))
        state->m_trait_bound_types.PushBack(type);
    }
  }
};

void CheckerState::SetReport(ReportKind kind)
{
  Assert(m_report_kind == RK_None);
  Assert(!m_base_bits.Empty());

  // get the last propagation we were taking when the error occurred.
  CheckerPropagate *propagate = m_stack.Back();

  // clear the alarm if there is one. at this point we're committed to making
  // the report and don't want the alarm interfering with the memory and
  // solver data.
  TimerAlarm::ClearActive();

  m_report_kind = kind;

  // change the direction taken for the propagation to the error report.
  if (propagate->m_where)
    delete propagate->m_where;
  propagate->m_where = new WhereNone(kind);

  // fixup any disconnected loops (frames with a loop parent but no caller),
  // adding caller connections for them.
  for (FrameId id = 1; id < m_frames.Size(); id++) {
    CheckerFrame *frame = m_frames[id];
    if (frame == NULL)
      continue;

    CheckerFrame *loop_parent_frame = frame->GetLoopParentFrame();
    if (loop_parent_frame && !frame->GetCallerFrame()) {
      PPoint point = frame->GetLoopParent().point;
      loop_parent_frame->ConnectCallee(frame, point, false);
    }
  }

  if (checker_dump.IsSpecified())
    Print();

  // fill in display information from the active propagation stack,
  // and get the trait information for the path.

  CheckerTraitVisitor visitor(this);

  for (size_t sind = 0; sind < m_stack.Size(); sind++) {
    CheckerPropagate *propagate = m_stack[sind];

    CheckerFrame *frame = propagate->m_frame;
    frame->m_display_propagate.PushBack(propagate);

    if (propagate->m_where) {
      if (Bit *bit = propagate->m_where->GetBit())
        bit->DoVisit(&visitor);
    }

    // add functions/inits from the frame.
    BlockId *id = frame->Memory()->GetId();
    if (id->Kind() == B_Function || id->Kind() == B_Initializer) {
      if (!m_trait_blocks.Contains(id))
        m_trait_blocks.PushBack(id);
    }
  }

  // list of empty propagates to delete.
  Vector<CheckerPropagate*> empty_propagates;

  // if we terminated the check inside a call stack, add empty propagations
  // for the callers of the termination point.
  CheckerFrame *frame = m_stack.Back()->m_frame;
  while (frame->GetCaller().id) {
    CheckerFrame *parent_frame = frame->GetCallerFrame();
    PPoint point = frame->GetCaller().point;

    CheckerPropagate *propagate =
      new CheckerPropagate(parent_frame, point, false);
    empty_propagates.PushBack(propagate);

    parent_frame->m_display_propagate.PushBack(propagate);
    frame = parent_frame;
  }

  AssertBaseBits();

  if (checker_fixup.IsSpecified()) {
    // try to get correct values for nonlinear operations.
    m_solver->TryFixUninterpreted();
  }

  // pin the solver's assignment in place for generating the path.
  m_solver->PinAssign();

  // check and make sure this is a correct assignment.
  m_solver->CheckAssignmentBits();

  if (checker_assign.IsSpecified())
    m_solver->PrintRawAssignment();

  // fill in the path for the root frame of the check. this will be at the
  // beginning of the m_base_frames list, the first one which was pushed on.
  CheckerFrame *base_frame = m_base_frames[0];
  CheckerFrame *root_frame = base_frame->GetPathRoot(true);

  m_path = new DisplayPath();

  PPoint entry_point = root_frame->CFG()->GetEntryPoint();
  DisplayFrame *disp_root = m_path->MakeFrame(root_frame, entry_point);
  m_path->m_frame_roots.PushBack(disp_root->m_index);

  m_solver->UnpinAssign();

  for (size_t ind = 0; ind < empty_propagates.Size(); ind++)
    delete empty_propagates[ind];
}

void CheckerState::PushContext()
{
  Assert(m_contexts.Size() == m_solver->GetContextCount());
  m_solver->PushContext();

  Vector<CheckerExpandItem> *context = new Vector<CheckerExpandItem>();
  m_contexts.PushBack(context);
}

void CheckerState::PopContext()
{
  Assert(m_contexts.Size() == m_solver->GetContextCount());
  m_solver->PopContext();

  Vector<CheckerExpandItem> *context = m_contexts.Back();
  m_contexts.PopBack();

  for (size_t ind = 0; ind < context->Size(); ind++) {
    const CheckerExpandItem &item = context->At(ind);

    // ignore the portions of contexts referring to frames which have since
    // been deleted.
    if (GetFrame(item.id) != NULL) {
      Assert(!item.expand->pending.Contains(item.exp));
      item.expand->pending.PushBack(item.exp);
    }
  }

  delete context;
}

CheckerFrame* CheckerState::MakeFrame(BlockId *cfg_id)
{
  BlockMemory *mcfg = GetBlockMemory(cfg_id);
  if (mcfg == NULL)
    return NULL;

  BlockCFG *cfg = mcfg->GetCFG();
  Assert(cfg);

  BlockSummary *summary = GetBlockSummary(cfg_id);
  Assert(summary);

  FrameId id = m_solver->MakeFrame(mcfg);
  Assert(id == m_frames.Size());

  CheckerFrame *frame = new CheckerFrame(this, id, cfg, mcfg, summary);
  m_frames.PushBack(frame);

  return frame;
}

size_t CheckerState::GetPropagateId()
{
  return ++m_propagate_count;
}

void CheckerState::DeleteFrame(CheckerFrame *frame)
{
  Assert(frame);
  Assert(m_frames[frame->Id()] == frame);

  m_frames[frame->Id()] = NULL;

  delete frame;
}

void CheckerState::Print(FrameId id)
{
  if (m_frames[id])
    m_frames[id]->Print();
  else
    logout << "(null)" << endl;
}

void CheckerState::Print()
{
  logout << "State:" << endl;
  for (size_t ind = 0; ind < m_frames.Size(); ind++) {
    if (m_frames[ind])
      m_frames[ind]->Print();
  }

  logout << "Stack:" << endl;
  for (size_t ind = 0; ind < m_stack.Size(); ind++)
    m_stack[ind]->Print();
}

void CheckerState::PrintTraits()
{
  for (size_t ind = 0; ind < m_trait_fields.Size(); ind++) {
    Field *field = m_trait_fields[ind];
    TypeCSU *csu_type = field->GetCSUType();
    logout << "TRAIT: Field '" << csu_type << "::" << field << "'" << endl;
  }

  for (size_t ind = 0; ind < m_trait_blocks.Size(); ind++) {
    BlockId *block = m_trait_blocks[ind];
    logout << "TRAIT: Block '" << block << "'" << endl;
  }

  if (!m_trait_blocks.Empty())
    logout << "TRAIT: BlockCount " << m_trait_blocks.Size() << endl;

  for (size_t ind = 0; ind < m_trait_bound_types.Size(); ind++) {
    Type *type = m_trait_bound_types[ind];
    logout << "TRAIT: BoundType " << type << endl;
  }

  if (m_trait_unsat)
    logout << "TRAIT: Unsatisfiable" << endl;

  if (m_trait_heap)
    logout << "TRAIT: HeapPropagate" << endl;

  for (size_t ind = 0; ind < m_trait_heap_fields.Size(); ind++) {
    Field *field = m_trait_heap_fields[ind];
    TypeCSU *csu_type = field->GetCSUType();
    logout << "TRAIT: HeapField '" << csu_type << "::" << field << "'" << endl;
  }
}

void CheckerState::PushBaseBit(Bit *bit, CheckerFrame *frame)
{
  // get the negation of the bit; we are interested in cases where the base
  // bits do *not* hold for some assignment.
  Bit *not_bit = Bit::MakeNot(bit);
  m_base_bits.PushBack(not_bit);
  m_base_frames.PushBack(frame);
}

void CheckerState::PopBaseBit()
{
  m_base_bits.PopBack();
  m_base_frames.PopBack();
}

void CheckerState::AssertBaseBits()
{
  Assert(!m_base_bits.Empty());

  for (size_t ind = 0; ind < m_base_bits.Size(); ind++) {
    Bit *bit = m_base_bits[ind];
    CheckerFrame *frame = m_base_frames[ind];
    m_solver->AddConstraint(frame->Id(), bit);
  }
}

NAMESPACE_XGILL_END
