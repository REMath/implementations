
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

#include <memory/mblock.h>
#include <memory/mstorage.h>
#include <solve/solver.h>
#include "path.h"
#include "where.h"

// control structures for path-exploration assertion checker.

NAMESPACE_XGILL_BEGIN

extern ConfigOption checker_fixup;
extern ConfigOption checker_assign;
extern ConfigOption checker_dump;

// forward declarations.
struct CheckerState;
struct CheckerPropagate;
struct CheckerPropagateHeap;

// the FrameId for a frame is its unique identifier, serving two roles.
// first, it is the offset into the m_frames vector in CheckerState, and will
// be used as an identifier for frames to refer to one another. this lets us
// delete frames without worrying too much about dangling pointers.
// second, it is the solver frame index used to distinguish lvalues
// and other leaf variables in asserted conditions involving the frame.
// zero for a frame index indicates a non-existent frame.

struct PointFrameId {
  PPoint point;
  FrameId id;

  PointFrameId()
    : point(0), id(0)
  {}

  PointFrameId(PPoint _point, FrameId _id)
    : point(_point), id(_id)
  {}
};

// set of expressions which either can or have been expanded as equalities
// between two frames.
struct CheckerExpandSet
{
  // name of this set.
  const char *name;

  // list of all expressions that can be expanded in this set.
  // grows monotonically.
  Vector<Exp*> exps;

  // subset of exps which are *not* currently expanded.
  // grows and shrinks as expressions are expanded and contexts are pushed
  // and popped.
  Vector<Exp*> pending;

  // point associated with this set, used only for callee expand sets.
  PPoint point;

  CheckerExpandSet(const char *_name, PPoint _point = 0)
    : name(_name), point(_point)
  {}

  // add an expression to this set if not already present and mark as pending.
  // return value is whether the add was successful.
  bool AddExp(Exp *exp)
  {
    if (!exps.Contains(exp)) {
      exps.PushBack(exp);
      pending.PushBack(exp);
      return true;
    }
    return false;
  }

  void PrintName() const
  {
    logout << name;
    if (point)
      logout << " " << point;
  }

  void Print() const
  {
    for (size_t ind = 0; ind < exps.Size(); ind++) {
      logout << "  ";
      PrintName();
      logout << " " << exps[ind];
      if (pending.Contains(exps[ind]))
        logout << " [pending]";
      logout << endl;
    }
  }
};

// information about a single checker expansion.
struct CheckerExpandItem
{
  // frame the expression set came from.
  FrameId id;

  // set the expression is being expanded for. internal to some CheckerFrame.
  CheckerExpandSet *expand;

  // expression being expanded.
  Exp *exp;

  CheckerExpandItem()
    : id(0), expand(NULL), exp(NULL)
  {}

  CheckerExpandItem(FrameId _id, CheckerExpandSet *_expand, Exp *_exp)
    : id(_id), expand(_expand), exp(_exp)
  {}

  void Print() const
  {
    logout << "frame " << id << ": ";
    expand->PrintName();
    logout << " " << exp;
  }
};

// node in the current checker exploration state. at any point in time
// some number of frames have been expanded for the callers and callees
// of the initial assertion. these frames form a tree (in the future,
// probably a forest) where links are caller/callee relationships.
class CheckerFrame
{
 public:
  CheckerFrame(CheckerState *state, FrameId id,
               BlockCFG *cfg, BlockMemory *mcfg, BlockSummary *summary);
  ~CheckerFrame();

  // accessor methods.

  // get the unique identifier of this frame (also a frame ID for the solver).
  FrameId Id() const { return m_id; }

  // get the parent state of this frame.
  CheckerState* State() const { return m_state; }

  // get the block, memory and summary for this frame.
  BlockCFG* CFG() const { return m_cfg; }
  BlockMemory* Memory() const { return m_mcfg; }
  BlockSummary* Summary() const { return m_summary; }

  // get the kind of block for this frame (function, loop, initializer).
  BlockKind Kind() const { return m_kind; }

  // get the last point in the block this frame covers.
  PPoint EndPoint() const { return m_end_point; }

  // print this frame to stdout.
  void Print();

  // connected frame methods. these return NULL if there is no such frame.

  // get the callee, loop tail, or skipped loop of this frame at point,
  // NULL/false if there is none.
  CheckerFrame* GetCalleeFrame(PPoint point);
  CheckerFrame* GetLoopTailFrame(PPoint point);
  bool IsSkippedLoop(PPoint point);

  // get all known callees of this frame.
  const Vector<PointFrameId>& GetAllCallees() { return m_callee_frames; }

  // get the point of any caller or loop parent.
  BlockPPoint GetCaller() const { return m_caller; }
  BlockPPoint GetLoopParent() const { return m_loop_parent; }

  // get the direct caller of this frame.
  CheckerFrame* GetCallerFrame();

  // get the loop parent which eventually invokes this frame.
  CheckerFrame* GetLoopParentFrame();

  // get the predecessor/successor for heap write frames.
  CheckerFrame* GetHeapPredecessorFrame();
  CheckerFrame* GetHeapSuccessorFrame();

  // get any callee frame the heap predecessor is performing reads for.
  CheckerFrame* GetCalleeHeapFrame();

  // get the translation kind to use when connecting this frame to a callee
  // at point. this is normally TRK_Callee, though it will be TRK_Point
  // if the callee is another iteration of the same loop.
  TranslateKind CalleeTranslateKind(PPoint point)
  {
    if (point == m_cfg->GetExitPoint())
      return TRK_Point;
    else
      return TRK_Callee;
  }

  // add equalities for all pending expand terms between this frame and
  // other connected frames. this should be called after one of the Connect
  // calls below, or whenever the equalities between the frame and its
  // neighbors need to be refreshed.
  void ExpandPendingExps();

  // connected frame modification methods.

  // set a direct call from this frame to callee_frame. if add_equalities
  // is set then equalities on between terms in this frame and callee_frame
  // may be added to the solver.
  void ConnectCallee(CheckerFrame *callee_frame, PPoint point,
                     bool add_equalities);

  // set child_frame as some iteration of the loop invoked by this frame.
  void ConnectLoopChild(CheckerFrame *child_frame, PPoint point);

  // set a loop tail relationship from this frame to tail_frame.
  void ConnectLoopTail(CheckerFrame *tail_frame, PPoint point);

  // set the discontinuous read frame for values written within this frame.
  void ConnectHeapRead(CheckerFrame *read_frame);

  // mark the specified point as skipping a loop.
  void AddSkipLoop(PPoint point);

  // mark the specified frame as the delayed heap callee of this frame.
  void SetCalleeHeapFrame(CheckerFrame *heap_frame);

  // undo operations performed by Connect calls.
  void DisconnectCallee(CheckerFrame *callee_frame, PPoint point);
  void DisconnectLoopChild(CheckerFrame *child_frame, PPoint point);
  void DisconnectLoopTail(CheckerFrame *tail_frame, PPoint point);
  void DisconnectHeapRead(CheckerFrame *read_frame);
  void RemoveSkipLoop(PPoint point);
  void UnsetCalleeHeapFrame();

  // if this frame has a loop parent, try pushing it up to the specified
  // caller if the caller is an unrolled iteration of the same loop.
  // this must have been connected to the caller with ConnectCallee.
  void PushCallerLoopParent(CheckerFrame *caller_frame);

  // assertion methods.

  // add an assertion within this frame.
  void AddAssert(Bit *bit, bool side_conditions = false);

  // specify point as the ending point of this frame, and assert the guard
  // at that point holds and any associated assumptions from the inference,
  // populating m_assumed_bits. if allow_point is set then assumptions may
  // be pulled in at point itself.
  void AssertPointGuard(PPoint point, bool allow_point);

  // push/pop extra assumed bits for this frame. pushing a bit will assert it.
  void PushAssumedBit(Bit *guard);
  void PopAssumedBit();

  // add all pending exps to the expand lists, and expand any pending
  // ExpVal uninterpreted values in the state's solver.
  void MarkPendingExps();

  // display methods.

  // get the root caller of this frame. if follow_heap_writes is specified
  // then heap predecessors will be traversed as well as callers.
  CheckerFrame* GetPathRoot(bool follow_heap_writes);

 private:
  // private fields.

  // parent checker state.
  CheckerState *m_state;

  // unique Id of this frame.
  FrameId m_id;

  // block/memory/summary for this frame.
  BlockCFG *m_cfg;
  BlockMemory *m_mcfg;
  BlockSummary *m_summary;

  // kind of block for this frame.
  BlockKind m_kind;

  // last point in the frame.
  PPoint m_end_point;

  // immediate caller to this frame or previous loop iteration,
  // empty if no caller has been instantiated.
  BlockPPoint m_caller;
  FrameId m_caller_frame;

  // whether to add equalities for caller_expand terms in the caller frame.
  bool m_caller_equalities;

  // for a loop iteration, specifies the outer frame which will invoke the
  // first iteration of the loop, if there is such a frame.
  BlockPPoint m_loop_parent;
  FrameId m_loop_parent_frame;

  // immediate callees to this frame which have been instantiated.
  Vector<PointFrameId> m_callee_frames;

  // last iterations of loops invoked by this frame (the first iteration
  // will be in m_callee_frames if it exists). not all invoked loops have
  // a last iteration, e.g. if the error occurs during their execution.
  // in these cases the loop will not be in m_loop_tail_frames.
  Vector<PointFrameId> m_loop_tail_frames;

  // points which have been marked as skipping a loop.
  Vector<PPoint> m_loop_skip_points;

  // any frame for a disconnected predecessor/successor connected by writes
  // performed by the first frame going to reads performed by the second frame.
  FrameId m_heap_predecessor_frame;
  FrameId m_heap_successor_frame;

  // exps which can be expanded in the caller to this frame.
  CheckerExpandSet m_caller_expand;

  // exps which can be expanded in the loop parent of this frame.
  // subset of m_caller_expand.
  CheckerExpandSet m_loop_parent_expand;

  // exps which can be expanded in the various callees of this frame.
  // the point in the sets distinguishes the different callees, and the
  // expressions themselves are relative to the exit state of that callee.
  Vector<CheckerExpandSet*> m_callee_expand;

  // if non-zero, indicates a callee of this frame for which heap propagation
  // needs to be performed.
  FrameId m_callee_heap_frame;

  // when heap propagation is done for a callee, this is set within the callee
  // to indicate the frame with m_heap_predecessor_frame set.
  FrameId m_caller_heap_frame;

 public:
  // public fields.

  // various bits which will always hold for this frame. these are used as
  // hints when generating sufficient conditions.
  Vector<Bit*> m_assumed_bits;

  // extra assumed bits for the particular path being explored through
  // this frame. these bits may change as the frame is revisited.
  Vector<Bit*> m_assumed_extra;

  // terms mentioned in assumed bits from annotations.
  Vector<Exp*> m_annotated_terms;

  // whether we have checked against previous asserted bits within this frame.
  // when checking the assert we assume previous assertions are correct
  // so that later redundant assertions can be easily proved.
  bool m_checked_assertions;

  // during path generation, indicates all the propagations on the checker
  // stack for this frame. the propagations closest to the bottom of the stack
  // (i.e. later in execution of the frame's CFG) will be listed first.
  Vector<CheckerPropagate*> m_display_propagate;
};

// print basic information about a frame to a stream.
inline OutStream& operator << (OutStream &out, const CheckerFrame *frame)
{
  Assert(frame);
  out << frame->Id();
  return out;
}

// state for an entire assertion check.
class CheckerState
{
 public:
  CheckerState(AssertKind assert_kind);
  ~CheckerState();

  // get the solver used for this assertion check.
  Solver* GetSolver() const { return m_solver; }

  // get the kind of assertion being checked.
  AssertKind GetAssertKind() const { return m_assert_kind; }

  // get the report kind for this check.
  ReportKind GetReportKind() const { return m_report_kind; }

  // set the report kind for this check, and constructs a display path
  // for the current checker stack.
  void SetReport(ReportKind kind);

  // CheckerState methods.

  // push and pop contexts on this frame. this operates both on the underlying
  // solver and on the expressions that have been expanded between frames.
  // never push/pop directly on the underlying solver.
  void PushContext();
  void PopContext();

  // get the topmost context that has been pushed.
  Vector<CheckerExpandItem>* TopContext() { return m_contexts.Back(); }

  // get the frame with the specified identifier.
  CheckerFrame* GetFrame(FrameId id) { return m_frames[id]; }

  // get a frame for the specified block, NULL if there is no memory
  // associated with that block.
  CheckerFrame* MakeFrame(BlockId *cfg_id);

  // get a fresh propagate ID.
  size_t GetPropagateId();

  // dispose of a frame created via MakeFrame.
  void DeleteFrame(CheckerFrame *frame);

  // print the frame with the specified id to stdout.
  void Print(FrameId id);

  // print this entire state to stdout.
  void Print();

  // print the traits for this state's report to stdout.
  void PrintTraits();

  // add bits to be asserted whenever the error is tested for satisfiability.
  void PushBaseBit(Bit *bit, CheckerFrame *frame);
  void PopBaseBit();

  // add assertions for all base bits that have been pushed. revert by
  // popping the solver context.
  void AssertBaseBits();

 private:
  // solver used to add new assertions and check equality.
  Solver *m_solver;

  // kind of assertion which is being checked.
  AssertKind m_assert_kind;

  // kind of report being generated, if any, from the final propagation.
  ReportKind m_report_kind;

  // all frames in use by this state. entries in this can be NULL for frames
  // which were used to explore different branches of the search space
  // and then erased.
  Vector<CheckerFrame*> m_frames;

  // number of propagations which have been generated for this state.
  size_t m_propagate_count;

  // stack of contexts indicating which expansions between frames
  // have been performed.
  Vector<Vector<CheckerExpandItem>*> m_contexts;

  // base bits and associated frames to be asserted when determining if the
  // error is satisfiable. this includes the negation of both the eventual
  // program assert as well as any heap invariants under consideration.
  Vector<Bit*> m_base_bits;
  Vector<CheckerFrame*> m_base_frames;

 public:
  // stack of active propagations, indicating the checker's current point
  // of exploration and all safe/sufficient bits up to that point.
  Vector<CheckerPropagate*> m_stack;

  // invariants and preconditions that are currently being checked or have
  // already been checked. assumptions are pulled in from these for newly
  // generated frames.
  Vector<WhereInvariant*> m_invariant_list;
  Vector<WherePrecondition*> m_precondition_list;

  // if we encounter heap propagation inside a call or loop body, remember
  // it here and propagate back out of the call/loop before handling the
  // possible writes for the heap propagation.
  CheckerPropagate *m_delayed_propagate_heap;

  // path filled in by SetReport.
  DisplayPath *m_path;

  // fields mentioned in the safe/sufficient bits on the path.
  Vector<Field*> m_trait_fields;

  // functions/inits traversed by the path.
  Vector<BlockId*> m_trait_blocks;

  // types of any bounds appearing in the safe/sufficient bits on the path.
  Vector<Type*> m_trait_bound_types;

  // there is a propagate with an unsatisfiable safe bit.
  bool m_trait_unsat;

  // heap propagation was performed.
  bool m_trait_heap;

  // any fields heap propagation was performed on.
  Vector<Field*> m_trait_heap_fields;
};

NAMESPACE_XGILL_END
