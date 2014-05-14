
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

#include "checker.h"
#include "propagate.h"

#include <imlang/storage.h>
#include <infer/expand.h>
#include <memory/baked.h>
#include <memory/mstorage.h>

NAMESPACE_XGILL_BEGIN

ConfigOption checker_verbose(CK_Flag, "ck-verbose", NULL,
                             "print taken steps for path checker");

ConfigOption checker_depth(CK_UInt, "ck-depth", "3",
                           "maximum recursive depth for a func/loop");

// returns whether the error condition is satisfiable within frame.
bool TestErrorSatisfiable(CheckerState *state, CheckerFrame *frame, Bit *bit)
{
  BlockMemory *mcfg = frame->Memory();
  Solver *solver = state->GetSolver();

  if (!solver->IsSatisfiable()) {
    if (checker_verbose.IsSpecified())
      logout << "CHECK: " << frame << ": Guard unsatisfiable: " << bit
             << " [" << bit->Hash() << "]" << endl;
    return false;
  }

  state->PushContext();
  state->AssertBaseBits();

  if (!solver->IsSatisfiable()) {
    if (checker_verbose.IsSpecified())
      logout << "CHECK: " << frame << ": Error unsatisfiable: " << bit
             << " [" << bit->Hash() << "]" << endl;
    state->PopContext();
    return false;
  }

  if (!frame->m_checked_assertions) {
    frame->m_checked_assertions = true;

    // check to see if the error is contradicted by previous assertions
    // in this frame. assert the previous assertions, but don't keep
    // them around past this function to avoid polluting the solver
    // with worthless extra checks.

    BlockSummary *sum = GetBlockSummary(mcfg->GetId());

    const Vector<AssertInfo> *asserts = sum->GetAsserts();
    size_t assert_count = VectorSize<AssertInfo>(asserts);

    for (size_t ind = 0; ind < assert_count; ind++) {
      const AssertInfo &info = asserts->At(ind);

      // only use the same kind of assertion to check for redundancy.
      if (info.kind != state->GetAssertKind())
        continue;

      if (info.cls != ASC_Check)
        continue;

      if (info.point < frame->EndPoint()) {
        // get the asserted condition relative to block entry.

        Bit *assert_value;
        mcfg->TranslateBit(TRK_Point, info.point, info.bit, &assert_value);

        Bit *point_guard = mcfg->GetGuard(info.point);
        Bit *imply_assert =
          Bit::MakeImply(point_guard, assert_value);

        solver->AddConstraint(frame->Id(), imply_assert);
      }
    }

    if (!solver->IsSatisfiable()) {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame
               << ": Unsatisfiable from assertions" << endl;

      state->PopContext();
      return false;
    }
  }

  state->PopContext();
  return true;
}

// at any point in checker execution, we have a forest of checker frames
// describing all portions of the program which have been expanded.
// tracing through these frames (possibly visiting a frame multiple times)
// is the checker stack, which corresponds to instances of CheckFrame
// on the program stack. Each CheckFrame has a CheckerPropagate associated
// with it indicating the current propagation state at that point
// on the stack.

// check for an error path in the specified frame, returning true and filling
// in the caller/callee children of frame if so. if no error path is found
// the state at exit will be the same as at entry.
bool CheckFrame(CheckerState *state, CheckerFrame *frame,
                CheckerPropagate *propagate);

// check propagation for each point bit in the specified frame. this is called
// both for the initial and intermediate checks of the assertion. assert_safe
// indicates that this is an initial check or an intermediate check of a heap
// invariant, and should be marked as a base bit/frame in the state.
bool CheckFrameList(CheckerState *state, CheckerFrame *frame,
                    PPoint point, bool allow_point, bool assert_safe,
                    Bit *base_bit, const GuardBitVector &point_list)
{
  // check if we are ignoring this function outright.
  BlockId *id = frame->CFG()->GetId();
  if (id->Kind() != B_Initializer && IgnoreFunction(id->BaseVar())) {
    if (checker_verbose.IsSpecified())
      logout << "CHECK: " << frame << ": Ignoring function" << endl;
    return false;
  }

  Solver *solver = state->GetSolver();

  if (!solver->IsSatisfiable()) {
    if (checker_verbose.IsSpecified())
      logout << "CHECK: " << frame << ": List unsatisfiable" << endl;
    return false;
  }

  for (size_t ind = 0; ind < point_list.Size(); ind++) {
    const GuardBit &gb = point_list[ind];

    state->PushContext();

    // the guard for the paths this safe bit takes are an extra assumed bit.
    frame->PushAssumedBit(gb.guard);

    // add side conditions and pending information from the bit.
    solver->AddSideConditions(frame->Id(), gb.bit);

    if (assert_safe)
      state->PushBaseBit(gb.bit, frame);

    if (TestErrorSatisfiable(state, frame, gb.bit)) {
      // error is feasible along these paths, construct a propagation
      // for the safe bit and continue exploration.
      CheckerPropagate propagate(frame, point, allow_point);
      propagate.m_id = state->GetPropagateId();

      propagate.FindTest(base_bit, gb.bit);

      state->m_stack.PushBack(&propagate);

      // check the frame against this propagation.
      if (CheckFrame(state, frame, &propagate))
        return true;

      // check if there was a soft timeout while we were finished
      // exploring this path. when the timeout occurs all satisfiable
      // queries become false so we will end up here.
      if (TimerAlarm::ActiveExpired()) {
        logout << "Timeout: ";
        PrintTime(TimerAlarm::ActiveElapsed());
        logout << endl;

        state->SetReport(RK_Timeout);
        return true;
      }

      state->m_stack.PopBack();
    }

    // no error along these paths, unwind the changes we made beforehand.
    if (assert_safe)
      state->PopBaseBit();
    frame->PopAssumedBit();
    state->PopContext();
  }

  return false;
}

// check a frame without any propagation. in this case the frame will be
// connected any existing caller until there is no existing caller, at which
// point a delayed heap propagation will be used if available.
bool CheckFrameSingle(CheckerState *state, CheckerFrame *frame, PPoint point)
{
  if (!TestErrorSatisfiable(state, frame, NULL))
    return false;

  state->PushContext();

  // push an empty propagation onto the stack for use in later display.
  CheckerPropagate propagate(frame, point, false);
  state->m_stack.PushBack(&propagate);

  if (CheckFrame(state, frame, NULL))
    return true;

  state->m_stack.PopBack();

  state->PopContext();
  return false;
}

// check a single caller to the specified frame at site 'where'.
// return value is whether an error path was found.
bool CheckSingleCaller(CheckerState *state, CheckerFrame *frame,
                       WherePrecondition *precondition, BlockPPoint where)
{
  CheckerFrame *caller_frame = frame->GetCallerFrame();
  CheckerFrame *loop_parent_frame = frame->GetLoopParentFrame();

  bool has_caller = (caller_frame != NULL);
  bool has_loop_parent = (loop_parent_frame != NULL);

  // whether we should keep the caller and callee frames disconnected
  // (unless they already are connected). this is done during loop propagation
  // if there is either a sufficient condition on the propagation or
  // no propagation at all (connecting frames for heap propagation),
  // ensuring we do not have to unroll the loop ad infinitum.
  bool keep_disconnected = false;

  if (frame->Kind() == B_Loop) {
    if (!precondition || precondition->IsIgnoreUnroll())
      keep_disconnected = true;
  }

  // special handling for loop unroll cases.
  if (frame->Kind() == B_Loop && frame->Memory()->GetId() == where.id) {

    // filter out unrolled loop iterations if the caller is disconnected.
    if (keep_disconnected) {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame << ": Skipping loop unroll" << endl;
      return false;
    }
  }

  // whether we had to create the caller frame.
  bool created_frame = false;

  // whether we need to connect this frame to the caller frame.
  bool connect_frame = false;

  if (has_caller) {
    // we should already have ensured this is a compatible caller.
    Assert(frame->GetCaller() == where);
    Assert(caller_frame);
  }
  else if (where == frame->GetLoopParent()) {
    // connecting to the loop parent of this frame.
    caller_frame = loop_parent_frame;
    Assert(caller_frame);

    connect_frame = true;
  }
  else {
    // no caller to connect to, we will have to make one.
    caller_frame = state->MakeFrame(where.id);

    if (caller_frame == NULL) {
      logout << "WARNING: Missing memory: '" << where.id << "'" << endl;
      return false;
    }

    BlockCFG *cfg = caller_frame->CFG();

    // check for call sites at loop isomorphic points. we will also see the
    // corresponding call site within the loop body, and handling that site
    // will also cover this one.
    if (cfg->IsLoopIsomorphic(where.point)) {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame << ": Caller is loop isomorphic" << endl;
      state->DeleteFrame(caller_frame);
      return false;
    }

    // for incremental analysis, make sure the call edge uses the current
    // version of the caller CFG. if there is a version mismatch then this
    // call site is for an older version of the CFG; if the current version
    // of the CFG still calls the function then there will be a separate
    // call edge for the updated call site.
    if (cfg->GetVersion() != where.version) {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame << ": Caller is an older version" << endl;
      state->DeleteFrame(caller_frame);
      return false;
    }

    caller_frame->AssertPointGuard(where.point, true);

    // check for a recursive function/loop call. if there is an existing
    // propagate for this function then just assert its safe/sufficient
    // bit within this caller_frame. TODO: this is unsound as we are not
    // accounting for the *other* parameters to the function which might
    // differ along the recursive calls.
    if (precondition && frame->Memory() == caller_frame->Memory()) {
      Bit *entry_bit = precondition->GetBit();
      caller_frame->AddAssert(entry_bit);
    }

    connect_frame = true;
    created_frame = true;
  }

  // if we are skipping from a loop iteration to the parent, make sure there
  // is a loop child relationship between the two.
  if (keep_disconnected) {
    Assert(frame->Kind() == B_Loop);
    Assert(caller_frame->Memory() != frame->Memory());

    // connect the caller frame as the loop parent if there isn't already one.
    if (loop_parent_frame) {
      Assert(loop_parent_frame == caller_frame);
    }
    else {
      caller_frame->ConnectLoopChild(frame, where.point);
    }
  }

  if (keep_disconnected)
    connect_frame = false;

  if (connect_frame) {
    caller_frame->ConnectCallee(frame, where.point, true);
    frame->PushCallerLoopParent(caller_frame);
  }

  // add any equalities we can between the frame and its caller.
  frame->ExpandPendingExps();

  if (precondition) {
    // get the safe bits for the caller frame.
    Bit *caller_base_bit;
    GuardBitVector caller_safe_list;
    precondition->GetCallerBits(caller_frame, where.point,
                                &caller_base_bit, &caller_safe_list);

    if (CheckFrameList(state, caller_frame, where.point, false, false,
                       caller_base_bit, caller_safe_list)) {
      return true;
    }
  }
  else {
    // continue the checker without any active propagation.
    if (CheckFrameSingle(state, caller_frame, where.point))
      return true;
  }

  if (!has_caller && frame->GetCaller().id != NULL)
    caller_frame->DisconnectCallee(frame, where.point);

  if (!has_loop_parent && frame->GetLoopParent().id != NULL)
    caller_frame->DisconnectLoopChild(frame, where.point);

  if (created_frame)
    state->DeleteFrame(caller_frame);

  return false;
}

bool CheckSkipLoop(CheckerState *state, CheckerFrame *frame, PPoint point,
                   WherePostcondition *postcondition)
{
  Assert(postcondition);
  Assert(postcondition->GetPoint() == point);

  // add equalities for each clobbered lvalue we care about in the loop.
  frame->AddSkipLoop(point);
  frame->ExpandPendingExps();

  // get the safe bits from before the loop.
  Bit *skip_base_bit;
  GuardBitVector skip_safe_list;
  postcondition->GetSkipLoopBits(&skip_base_bit, &skip_safe_list);

  if (CheckFrameList(state, frame, point, false, false,
                     skip_base_bit, skip_safe_list)) {
    return true;
  }

  frame->RemoveSkipLoop(point);
  return false;
}

// consumes a reference on callee.
bool CheckSingleCallee(CheckerState *state, CheckerFrame *frame, PPoint point,
                       WherePostcondition *postcondition,
                       BlockId *callee, bool direct)
{
  Assert(postcondition);
  Assert(postcondition->GetPoint() == point);

  BlockCFG *cfg = frame->Memory()->GetCFG();
  bool is_call = cfg->PointEdgeIsCall(point);

  CheckerFrame *callee_frame;
  if (is_call)
    callee_frame = frame->GetCalleeFrame(point);
  else
    callee_frame = frame->GetLoopTailFrame(point);

  // we should be going strictly backwards, and thus should never be
  // able to visit the exit point of a callee more than once.
  Assert(!callee_frame);

  callee_frame = state->MakeFrame(callee);

  if (callee_frame == NULL) {
    // there are two ways we can get here:
    // 1. we saw the definition but timed out generating the memory.
    //    emit a warning.
    // 2. we never saw a definition. emit a warning in the indirect call case,
    //    make a report in the direct call case. we should really make a report
    //    in all cases, but the indirect callgraph needs some more work.

    BlockCFG *cfg = GetBlockCFG(callee);
    if (!cfg) {
      const char *kind = direct ? "direct" : "indirect";
      logout << "WARNING: Missing " << kind
             << " callee: '" << callee << "'" << endl;

      if (!direct)
        return false;

      // make an empty propagation for before the call.
      CheckerPropagate propagate(frame, point, false);
      state->m_stack.PushBack(&propagate);

      state->SetReport(RK_NoCallee);
      return true;
    }

    logout << "WARNING: Missing memory: '" << callee << "'" << endl;
    return false;
  }

  PPoint exit_point = callee_frame->Memory()->GetCFG()->GetExitPoint();
  callee_frame->AssertPointGuard(exit_point, true);

  for (size_t ind = 0; ind < state->m_stack.Size(); ind++) {
    CheckerPropagate *propagate = state->m_stack[ind];
    if (propagate->m_frame->Memory() == callee_frame->Memory()) {
      Bit *bit = NULL;
      callee_frame->Memory()->TranslateBit(TRK_Point, exit_point, propagate->m_base_bit, &bit);
      callee_frame->AddAssert(bit);
    }
  }

  if (is_call) {
    frame->ConnectCallee(callee_frame, point, true);
  }
  else {
    // we are getting the last iteration of the loop so there is no direct
    // callee to connect yet.
    frame->ConnectLoopTail(callee_frame, point);
  }

  // add the exit equalities for any callee_expand in frame and caller_expand
  // in callee_frame.
  frame->ExpandPendingExps();
  callee_frame->ExpandPendingExps();

  // get the safe bits for the callee frame.
  Bit *callee_base_bit;
  GuardBitVector callee_safe_list;
  postcondition->GetCalleeBits(callee_frame,
                               &callee_base_bit, &callee_safe_list);

  if (CheckFrameList(state, callee_frame, exit_point, false, false,
                     callee_base_bit, callee_safe_list)) {
    return true;
  }

  if (is_call)
    frame->DisconnectCallee(callee_frame, point);
  else
    frame->DisconnectLoopTail(callee_frame, point);

  state->DeleteFrame(callee_frame);
  return false;
}

// information about an lvalue which may be written in some block,
// affecting a future heap read.
struct HeapWriteInfo
{
  // block which writes to the lvalue.
  BlockMemory *mcfg;

  // lvalue we are interested in writes on. this is either a global lvalue or
  // is an offset from a CSU.
  Exp *lval;

  // the expression for lval relative to the point the write occurs.
  Exp *base_lval;

  // conditions in mcfg where lval is not actually written.
  // these are functionally determined from mcfg and lval.
  Vector<Bit*> exclude;

  HeapWriteInfo()
    : mcfg(NULL), lval(NULL), base_lval(NULL)
  {}

  bool operator == (const HeapWriteInfo &o) {
    // two writes to the same lval but through different point-relative
    // expressions are considered equivalent.
    return mcfg == o.mcfg && lval == o.lval;
  }

  static int Compare(const HeapWriteInfo &v0, const HeapWriteInfo &v1)
  {
    int cmp = BlockId::Compare(v0.mcfg->GetId(), v1.mcfg->GetId());
    if (cmp) return cmp;

    return Exp::Compare(v0.lval, v1.lval);
  }
};

bool CheckSingleHeapWrite(CheckerState *state, CheckerFrame *frame,
                          CheckerFrame *heap_frame, WhereInvariant *invariant,
                          const HeapWriteInfo &write)
{
  Assert(invariant);

  if (checker_verbose.IsSpecified())
    logout << "CHECK: " << frame
           << ": Checking single heap write: " << write.mcfg->GetId()
           << ": " << write.lval << endl;

  if (frame->Memory()->GetId()->Kind() == B_Initializer) {
    // rule out cases where another function executed before a static
    // initializer. TODO: this case can occur in C++ constructors and the
    // functions they call, should revisit this behavior.
    if (write.mcfg->GetId()->Kind() != B_Initializer) {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame
               << ": Write is not in a static initializer" << endl;

      return false;
    }
  }

  CheckerFrame *write_frame = state->MakeFrame(write.mcfg->GetId());
  Assert(write_frame && write_frame->Memory() == write.mcfg);

  PPoint exit_point = write.mcfg->GetCFG()->GetExitPoint();
  write_frame->AssertPointGuard(exit_point, true);

  // assert the lvalue is actually updated within this frame. these bits
  // are never explicitly popped, they get dropped when the frame is deleted.
  for (size_t ind = 0; ind < write.exclude.Size(); ind++) {
    Bit *bit = write.exclude[ind];
    Bit *not_bit = Bit::MakeNot(bit);
    write_frame->PushAssumedBit(not_bit);
  }

  // connect the heap read and write frames.
  write_frame->ConnectHeapRead(heap_frame);

  // for type invariants, try to reconstruct the CSU exp for the write frame.
  Exp *write_csu = NULL;
  Exp *base_csu = NULL;
  if (invariant->GetCSU()) {
    write_csu = invariant->GetWriteCSU(write.lval);
    if (write_csu == NULL) {
      CheckerPropagate propagate(write_frame, exit_point, false);
      state->m_stack.PushBack(&propagate);

      state->SetReport(RK_UnknownCSU);
      return true;
    }

    // OK if we couldn't figure out the point-relative CSU, will just be
    // a more confusing UI message.
    base_csu = invariant->GetWriteCSU(write.base_lval);
  }

  // get the safe bits for the write frame.
  Bit *write_safe_bit;
  GuardBitVector write_safe_list;
  invariant->GetHeapBits(write_frame, write_csu, base_csu,
                         &write_safe_bit, &write_safe_list);

  if (CheckFrameList(state, write_frame, exit_point, true, true,
                     write_safe_bit, write_safe_list)) {
    return true;
  }

  write_frame->DisconnectHeapRead(heap_frame);
  state->DeleteFrame(write_frame);

  return false;
}

void GetMatchingHeapWrites(const EscapeAccess &heap_write,
                           Vector<HeapWriteInfo> *writes)
{
  BlockId *id = heap_write.where.id;
  BlockMemory *mcfg = GetBlockMemory(id);

  if (mcfg == NULL) {
    logout << "WARNING: Missing memory: '" << id << "'" << endl;
    return;
  }

  BlockCFG *cfg = mcfg->GetCFG();

  // for incremental analysis, make sure the write CFG uses the right version.
  // as for checking callers, if the CFG has changed but the new one still
  // has a matching write, we will see an escape access for the new CFG.
  if (cfg->GetVersion() != heap_write.where.version) {
    if (checker_verbose.IsSpecified())
      logout << "CHECK: Write is an older version: "
             << heap_write.where.id << ": "
             << heap_write.where.version << endl;
    return;
  }

  PPoint point = heap_write.where.point;
  PPoint exit_point = mcfg->GetCFG()->GetExitPoint();

  // find a point-relative lvalue written at the write point with
  // the sanitized representation from the heap_write trace.
  // TODO: we only match against direct assignments in the CFG for now,
  // ignoring structural copies (which are simple recursive writes).

  PEdge *edge = cfg->GetSingleOutgoingEdge(point);
  Exp *point_lval = NULL;

  if (PEdgeAssign *nedge = edge->IfAssign())
    point_lval = nedge->GetLeftSide();
  else if (PEdgeCall *nedge = edge->IfCall())
    point_lval = nedge->GetReturnValue();

  bool lval_matches = false;

  if (point_lval) {
    if (Exp *new_point_lval = Trace::SanitizeExp(point_lval)) {
      lval_matches = (new_point_lval == heap_write.target->GetValue());
    }
  }

  if (!lval_matches)
    return;

  // it would be nice to remove Val() expressions from this list, but we can't
  // do that as lvalues in memory assignments can contain Val and we want to
  // see the effects of those assignments. TODO: fix.
  GuardExpVector lval_res;
  mcfg->TranslateExp(TRK_Point, point, point_lval, &lval_res);

  for (size_t ind = 0; ind < lval_res.Size(); ind++) {
    const GuardExp &lv = lval_res[ind];

    HeapWriteInfo info;
    info.mcfg = mcfg;
    info.lval = lv.exp;
    info.base_lval = point_lval;

    // look for a condition where the lvalue is not written.
    GuardExpVector exit_vals;
    info.mcfg->GetValComplete(info.lval, NULL, exit_point, &exit_vals);

    for (size_t ind = 0; ind < exit_vals.Size(); ind++) {
      const GuardExp &val = exit_vals[ind];

      // exclude cases where the lvalue refers to its value at block entry.
      if (ExpDrf *nval = val.exp->IfDrf()) {
        if (nval->GetTarget() == info.lval)
          info.exclude.PushBack(val.guard);
      }
    }

    if (!writes->Contains(info))
      writes->PushBack(info);
  }
}

// check all possible heap writes which could affect the propagating heap reads
// in propagate. frame indicates the actual frame to connect the heap write
// frames to, heap_frame indicates where the heap read occurred.
bool CheckHeapWrites(CheckerState *state, CheckerFrame *frame,
                     CheckerFrame *heap_frame, WhereInvariant *invariant)
{
  Assert(invariant);

  if (checker_verbose.IsSpecified())
    logout << "CHECK: " << frame
           << ": Checking heap writes from " << heap_frame << endl;

  frame->SetCalleeHeapFrame(heap_frame);

  TypeCSU *csu = invariant->GetCSU();
  Bit *bit = invariant->GetBit();

  // if there is already an equivalent known heap invariant, this is direct
  // recursion and we're done.
  for (size_t ind = 0; ind < state->m_invariant_list.Size(); ind++) {
    WhereInvariant *existing = state->m_invariant_list[ind];
    if (existing->GetCSU() == csu && existing->GetBit() == bit) {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame
               << ": Direct recursive invariant" << endl;
      return false;
    }
  }

  // duplicate the invariant and add it to the state for handling recursive
  // reads. either we will successfully check this invariant and can assume
  // it at all further reads, or we will fail and generate a report. either
  // way we don't need to worry about removing this invariant.

  WhereInvariant *dupe_invariant = new WhereInvariant(csu, NULL, bit);
  state->m_invariant_list.PushBack(dupe_invariant);

  // list of all the written lvalues to propagate to.
  Vector<HeapWriteInfo> writes;

  Vector<Trace*> heap_traces;
  GetUpdateTraces(invariant->GetBit(), &heap_traces);

  for (size_t ind = 0; ind < heap_traces.Size(); ind++) {
    Trace *heap_trace = heap_traces[ind];

    EscapeAccessSet *access_set = EscapeAccessCache.Lookup(heap_trace);

    if (access_set) {
      for (size_t aind = 0; aind < access_set->GetAccessCount(); aind++) {
        const EscapeAccess &access = access_set->GetAccess(aind);
        if (access.kind == EAK_Write)
          GetMatchingHeapWrites(access, &writes);
      }
    }

    EscapeAccessCache.Release(heap_trace);
  }

  if (checker_verbose.IsSpecified())
    logout << "CHECK: " << frame
           << ": Found " << writes.Size() << " matching writes" << endl;

  SortVector<HeapWriteInfo,HeapWriteInfo>(&writes);

  bool res = false;

  for (size_t wind = 0; wind < writes.Size(); wind++) {
    const HeapWriteInfo &write = writes[wind];
    state->PushContext();

    if (CheckSingleHeapWrite(state, frame, heap_frame, invariant, write)) {
      res = true;
      break;
    }

    state->PopContext();
  }

  if (res)
    return true;

  frame->UnsetCalleeHeapFrame();
  return false;
}

bool CheckFrame(CheckerState *state, CheckerFrame *frame,
                CheckerPropagate *propagate)
{
  Assert(!state->GetReportKind());

  BlockMemory *mcfg = frame->Memory();
  BlockCFG *cfg = mcfg->GetCFG();
  BlockId *id = cfg->GetId();

  if (checker_verbose.IsSpecified()) {
    logout << "CHECK: " << frame << ": Entering " << id << endl;
    if (propagate)
      propagate->Print();
  }

  Where *where = propagate ? propagate->m_where : NULL;

  // check if we should terminate the search at this point (with or without
  // generating a report).
  if (where && where->IsNone()) {
    WhereNone *nwhere = where->AsNone();
    ReportKind kind = nwhere->GetReportKind();

    if (kind == RK_None) {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame << ": Ignoring" << endl;
      return false;
    }
    else {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame << ": Propagation failed" << endl;
      state->SetReport(kind);
      return true;
    }
  }

  // check for other propagations on the stack with frames for the same block,
  // and block the recursion if we exceed the checker's depth. we assume that
  // if we're ever going to terminate in the presence of recursion, we will
  // do so quickly.

  if (propagate) {
    if (uint32_t depth = checker_depth.UIntValue()) {
      Vector<CheckerFrame*> recurse_frames;

      for (size_t ind = 0; ind < state->m_stack.Size(); ind++) {
        CheckerFrame *other_frame = state->m_stack[ind]->m_frame;
        if (other_frame != frame && other_frame->Memory() == mcfg &&
            !recurse_frames.Contains(other_frame))
          recurse_frames.PushBack(other_frame);
      }

      if (recurse_frames.Size() >= depth) {
        state->SetReport(RK_Recursion);
        return true;
      }
    }
  }

  // check if we are propagating into some callee.
  if (where && where->IsPostcondition()) {
    WherePostcondition *nwhere = where->AsPostcondition();

    // expand the callee at the specified point.
    PPoint point = nwhere->GetPoint();
    PEdge *edge = cfg->GetSingleOutgoingEdge(point);

    if (edge->IsLoop()) {
      // expanding data from a loop. first try the case that the loop
      // does not execute at all.

      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame
               << ": Trying to skip loop at " << point << endl;

      state->PushContext();

      if (CheckSkipLoop(state, frame, point, nwhere))
        return true;

      state->PopContext();
    }

    if (BlockId *callee = edge->GetDirectCallee()) {
      // easy case, there is only a single callee.

      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame
               << ": Expanding single callee at " << point
               << ": " << callee << endl;

      state->PushContext();

      if (CheckSingleCallee(state, frame, point, nwhere, callee, true))
        return true;

      state->PopContext();
    }
    else {
      // iterate through all the possible callees

      Variable *function = id->BaseVar();
      CallEdgeSet *callees = CalleeCache.Lookup(function);

      Vector<Variable*> callee_vars;

      if (callees) {
        for (size_t eind = 0; eind < callees->GetEdgeCount(); eind++) {
          const CallEdge &edge = callees->GetEdge(eind);
          if (edge.where.id == id && edge.where.point == point)
            callee_vars.PushBack(edge.callee);
        }
      }

      SortVector<Variable*,Variable>(&callee_vars);

      for (size_t cind = 0; cind < callee_vars.Size(); cind++) {
        Variable *callee = callee_vars[cind];

        if (checker_verbose.IsSpecified())
          logout << "CHECK: " << frame
                 << ": Expanding indirect callee at " << point
                 << ": " << callee << endl;

        BlockId *callee_id = BlockId::Make(B_Function, callee);

        state->PushContext();

        if (CheckSingleCallee(state, frame, point,
                              nwhere, callee_id, false)) {
          CalleeCache.Release(function);
          return true;
        }

        state->PopContext();
      }

      if (callee_vars.Empty()) {
        if (checker_verbose.IsSpecified())
          logout << "CHECK: " << frame
                 << ": No callees to expand at " << point << endl;
      }

      CalleeCache.Release(function);
    }

    return false;
  }

  // any precondition we have to propagate up to the callers.
  WherePrecondition *precondition = NULL;
  if (where)
    precondition = where->IfPrecondition();

  // whether we will be reconnecting to the caller without any
  // propagation information.
  bool reconnect_caller = false;

  if (precondition) {
    Bit *bit = precondition->GetBit();
    WherePrecondition *dupe_precondition = new WherePrecondition(mcfg, bit);
    state->m_precondition_list.PushBack(dupe_precondition);
  }
  else {
    // we will propagate to the caller regardless if there is already a caller
    // hooked up or if we are inside a loop body.

    if (frame->GetCaller().id != NULL)
      reconnect_caller = true;

    if (frame->Kind() == B_Loop)
      reconnect_caller = true;
  }

  if (propagate && reconnect_caller) {
    // check to see if we are delaying any heap propagation.
    if (where->IsInvariant()) {
      Assert(state->m_delayed_propagate_heap == NULL);
      state->m_delayed_propagate_heap = propagate;
    }
  }
  else if (!precondition && !reconnect_caller) {
    // check to see if we are performing heap propagation.

    if (state->m_delayed_propagate_heap) {
      Assert(propagate == NULL);
      CheckerPropagate *heap_propagate = state->m_delayed_propagate_heap;
      state->m_delayed_propagate_heap = NULL;

      WhereInvariant *invariant = heap_propagate->m_where->AsInvariant();

      if (CheckHeapWrites(state, frame, heap_propagate->m_frame, invariant))
        return true;

      state->m_delayed_propagate_heap = heap_propagate;
      return false;
    }
    else if (where && where->IsInvariant()) {
      return CheckHeapWrites(state, frame, frame, where->AsInvariant());
    }

    Assert(propagate);

    // don't need to expand the callers or anything else.
    // we can finally terminate propagation with an error report.

    if (checker_verbose.IsSpecified())
      logout << "CHECK: " << frame
             << ": Nothing to expand, finishing" << endl;

    state->SetReport(RK_Finished);
    return true;
  }

  if (frame->GetCaller().id != NULL) {
    // just propagate to the existing caller.

    if (checker_verbose.IsSpecified())
      logout << "CHECK: " << frame
             << ": Returning to caller" << endl;

    state->PushContext();

    if (CheckSingleCaller(state, frame, precondition, frame->GetCaller()))
      return true;

    state->PopContext();
  }
  else if (id->Kind() == B_Function) {
    // propagate to all callers to the function.

    Variable *function = id->BaseVar();
    CallEdgeSet *callers = CallerCache.Lookup(function);

    Vector<BlockPPoint> caller_points;

    for (size_t eind = 0; callers && eind < callers->GetEdgeCount(); eind++) {
      const CallEdge &edge = callers->GetEdge(eind);
      Assert(edge.callee == function);

      caller_points.PushBack(edge.where);
    }

    SortVector<BlockPPoint,BlockPPoint>(&caller_points);

    for (size_t cind = 0; cind < caller_points.Size(); cind++) {
      BlockPPoint caller = caller_points[cind];

      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame
               << ": Checking caller: " << caller << endl;

      state->PushContext();

      if (CheckSingleCaller(state, frame, precondition, caller)) {
        CallerCache.Release(function);
        return true;
      }

      state->PopContext();
    }

    if (caller_points.Empty()) {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame << ": No callers to expand" << endl;
    }

    CallerCache.Release(function);
  }
  else if (id->Kind() == B_Loop) {
    // check all possible callers of the loop. unroll an iteration before
    // checking the parents so that if we can't figure out a sufficient
    // condition for the loop we will stop exploration quickly.

    // unroll another iteration of the loop.

    if (checker_verbose.IsSpecified())
      logout << "CHECK: " << frame
             << ": Unrolling loop iteration" << endl;

    state->PushContext();

    BlockPPoint recursive_caller(id, cfg->GetExitPoint());
    if (CheckSingleCaller(state, frame, precondition, recursive_caller))
      return true;

    state->PopContext();

    // check the parents which can initially invoke this loop.

    if (frame->GetLoopParent().id != NULL) {
      if (checker_verbose.IsSpecified())
        logout << "CHECK: " << frame
               << ": Checking existing loop parent: "
               << frame->GetLoopParent() << endl;

      state->PushContext();

      if (CheckSingleCaller(state, frame, precondition,
                            frame->GetLoopParent()))
        return true;

      state->PopContext();
    }
    else {
      for (size_t pind = 0; pind < cfg->GetLoopParentCount(); pind++) {
        BlockPPoint where = cfg->GetLoopParent(pind);

        if (checker_verbose.IsSpecified())
          logout << "CHECK: " << frame
                 << ": Checking loop parent: " << where << endl;

        state->PushContext();

        if (CheckSingleCaller(state, frame, precondition, where))
          return true;

        state->PopContext();
      }
    }
  }
  else if (id->Kind() == B_Initializer) {
    // initializers don't have callers, can just ignore this.
    // TODO: should address why this code is being reached in the first place.
    if (checker_verbose.IsSpecified())
      logout << "CHECK: " << frame << ": Initializer has no callers" << endl;
    return false;
  }
  else {
    // unknown type of block.
    Assert(false);
  }

  // if we set the state's delayed heap propagation then unset it.
  if (propagate && state->m_delayed_propagate_heap == propagate)
    state->m_delayed_propagate_heap = NULL;

  return false;
}

CheckerState* CheckAssertion(BlockId *id, const AssertInfo &info)
{
  Assert(info.cls == ASC_Check);

  CheckerState *state = new CheckerState(info.kind);

  // get a frame for the block containing the asserted condition.
  CheckerFrame *base_frame = state->MakeFrame(id);
  Assert(base_frame);

  // point to translate the assertion at.
  PPoint use_point = 0;
  bool allow_point = true;

  if (info.kind == ASK_Invariant) {
    // for invariants we assert at exit from the block. the path must still
    // go through the point where the write occurred.
    Bit *guard = base_frame->Memory()->GetGuard(info.point);
    base_frame->AddAssert(guard);
    use_point = base_frame->Memory()->GetCFG()->GetExitPoint();
  }
  else {
    // the assert must hold at the point of the assertion (!).
    use_point = info.point;

    // pull in annotations at this point except when checking other
    // annotations. this is only important for point annotations added
    // via the web UI, which don't have an outgoing annotation edge.
    if (info.kind == ASK_Annotation || info.kind == ASK_AnnotationRuntime)
      allow_point = false;
  }

  base_frame->AssertPointGuard(use_point, allow_point);

  // get safe bits for the initial assertion.
  GuardBitVector base_safe_list;
  Where::GetAssertBits(base_frame, use_point, info.bit, &base_safe_list);

  CheckFrameList(state, base_frame, use_point,
                 false, true, info.bit, base_safe_list);

  return state;
}

NAMESPACE_XGILL_END
