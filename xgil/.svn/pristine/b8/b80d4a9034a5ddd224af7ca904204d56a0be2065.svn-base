
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

#include "loopsplit.h"
#include "storage.h"

NAMESPACE_XGILL_BEGIN

// topsort the graph, marking backedges
// loop heads are those at the target of a backedge

// loop graph is reachability graph between loop heads over non back edges.
// this is a DAG even if there are irreducible loops. visit leaf loops in
// this graph first, thus ensuring split bodies do not contain loops that
// haven't been handled yet

// for each loop:
// add a split body: the set of edges reachable from the loop head which reach
//   a back edge on the loop over non-backedge paths.
// remove backedges on the loop from the CFG.
// insert an edge at the loop head invoking the split body

// table for the points reachable from CFG entry.
// computed by GetEntryReachable()
PPointHash* entry_reach_table = NULL;

// table for the 'loophead dominates p' relation.
// computed by GetLoopBackEdges()
PPointPairHash *dominate_table = NULL;

// table for the loop backedges.
// computed by GetLoopBackEdges()
PEdgeHash *backedge_table = NULL;

// table for the 'loophead reaches p over non-backedges' relation.
// computed by GetLoopReachable()
PPointPairHash *reach_table = NULL;

// table for the 'loophead contains p in its body' relation.
// computed by GetLoopBody()
PPointPairHash *body_table = NULL;

// table for the 'loophead's body are the plist points' relation.
// computed by GetLoopBody()
PPointListHash *body_list_table = NULL;

void SetupTables()
{
  Assert(entry_reach_table == NULL);
  Assert(dominate_table == NULL);
  Assert(backedge_table == NULL);
  Assert(reach_table == NULL);
  Assert(body_table == NULL);
  Assert(body_list_table == NULL);

  entry_reach_table = new PPointHash();
  dominate_table = new PPointPairHash();
  backedge_table = new PEdgeHash();
  reach_table = new PPointPairHash();
  body_table = new PPointPairHash();
  body_list_table = new PPointListHash();
}

void CleanupTables()
{
  Assert(entry_reach_table != NULL);
  Assert(dominate_table != NULL);
  Assert(backedge_table != NULL);
  Assert(reach_table != NULL);
  Assert(body_table != NULL);
  Assert(body_list_table != NULL);

  delete entry_reach_table;
  entry_reach_table = NULL;

  delete dominate_table;
  dominate_table = NULL;

  delete backedge_table;
  backedge_table = NULL;

  delete reach_table;
  reach_table = NULL;

  delete body_table;
  body_table = NULL;

  delete body_list_table;
  body_list_table = NULL;
}

// compute the points in the CFG reachable from the entry point.
void GetEntryReachable(BlockCFG *cfg)
{
  // worklist items are reachable points whose outgoing edges have
  // not been examined
  Vector<PPoint> worklist;

  PPoint entry = cfg->GetEntryPoint();
  entry_reach_table->Insert(entry);
  worklist.PushBack(entry);

  while (!worklist.Empty()) {
    PPoint back = worklist.Back();
    worklist.PopBack();

    const Vector<PEdge*>& outgoing = cfg->GetOutgoingEdges(back);
    for (size_t oind = 0; oind < outgoing.Size(); oind++) {
      PEdge *edge = outgoing[oind];
      PPoint next = edge->GetTarget();

      // already did this target
      if (entry_reach_table->Lookup(next))
        continue;

      entry_reach_table->Insert(next);
      worklist.PushBack(next);
    }
  }
}

// determine whether loophead is a reducible loop with backedges in cfg.
// fill in dominate_table with the points dominated by loophead,
// and add as backedges any edge going to loophead which is itself
// dominated by loophead. return true if any backedges were found.
bool GetLoopBackedges(BlockCFG *cfg, PPoint loophead)
{
  // compute the nodes reachable from the entry point other than
  // through start. the dominated points are the dual of this set.

  // points reachable from the start according to the above criteria
  PPointHash reachable;

  // worklist items are points in reachable whose outgoing edges have
  // not been examined
  Vector<PPoint> worklist;

  if (!entry_reach_table->Lookup(loophead))
    return false;

  PPoint entry = cfg->GetEntryPoint();
  reachable.Insert(entry);
  worklist.PushBack(entry);

  while (!worklist.Empty()) {
    PPoint back = worklist.Back();
    worklist.PopBack();

    const Vector<PEdge*>& outgoing = cfg->GetOutgoingEdges(back);
    for (size_t oind = 0; oind < outgoing.Size(); oind++) {
      PEdge *edge = outgoing[oind];
      PPoint next = edge->GetTarget();

      if (next == loophead)
        continue;

      // already did this target
      if (reachable.Lookup(next))
        continue;

      reachable.Insert(next);
      worklist.PushBack(next);
    }
  }

  // compute the set of dominated points. this is the difference
  // between the points reachable from the CFG entry, and the points
  // in the reach table we just computed.
  for (PPoint point = 1; point <= cfg->GetPointCount(); point++) {
    if (!reachable.Lookup(point) && entry_reach_table->Lookup(point))
      dominate_table->Insert(PPointPair(loophead, point));
  }

  // backedges on the loophead are incoming edges whose source is
  // dominated by the loophead
  bool found_backedge = false;
  const Vector<PEdge*> &incoming = cfg->GetIncomingEdges(loophead);
  for (size_t eind = 0; eind < incoming.Size(); eind++) {
    PEdge *edge = incoming[eind];
    if (dominate_table->Lookup(PPointPair(loophead, edge->GetSource()))) {
      backedge_table->Insert(edge);
      found_backedge = true;
    }
  }

  return found_backedge;
}

// get the set of points reachable from loophead over paths
// that do not go through a backedge. if loophead itself is
// reachable, it is irreducible and those new edges to it are added
// as backedges. return value is true iff the loop is irreducible.
bool GetLoopReachable(BlockCFG *cfg, PPoint loophead)
{
  // worklist items are points in reach_table whose outgoing edges
  // have not been examined
  Vector<PPoint> worklist;

  if (!entry_reach_table->Lookup(loophead))
    return false;

  reach_table->Insert(PPointPair(loophead, loophead));
  worklist.PushBack(loophead);

  bool found_irreducible = false;

  while (!worklist.Empty()) {
    PPoint back = worklist.Back();
    worklist.PopBack();

    const Vector<PEdge*>& outgoing = cfg->GetOutgoingEdges(back);
    for (size_t oind = 0; oind < outgoing.Size(); oind++) {
      PEdge *edge = outgoing[oind];
      PPoint next = edge->GetTarget();

      if (backedge_table->Lookup(edge))
        continue;

      if (next == loophead) {
        // we're in an irreducible loop. add the new edge to backedge_table.
        backedge_table->Insert(edge);
        found_irreducible = true;
        continue;
      }

      if (!reach_table->Insert(PPointPair(loophead, next)))
        worklist.PushBack(next);
    }
  }

  return found_irreducible;
}

// fill in the body of loophead. points in the body are those which
// are reachable from loophead over non-backedges, and which themselves
// reach a backedge for loophead. note that in the case of loop nesting,
// a point may be contained in the body of multiple loops.
// if any irreducible edges are found (edges incoming to a body point
// other than loophead whose source is not in the body), those edges
// are added to irreducible_edges
void GetLoopBody(BlockCFG *cfg, PPoint loophead,
                 Vector<PEdge*> *irreducible_edges)
{
  Vector<PPoint> *body_list = body_list_table->Lookup(loophead, true);
  Assert(body_list->Empty());

  // worklist items are points which reach a loop backedge but whose
  // incoming edges have not yet been examined.
  Vector<PPoint> worklist;

  const Vector<PEdge*> &head_incoming = cfg->GetIncomingEdges(loophead);
  for (size_t iind = 0; iind < head_incoming.Size(); iind++) {
    PEdge *edge = head_incoming[iind];
    PPoint source = edge->GetSource();

    if (backedge_table->Lookup(edge)) {
      Assert(reach_table->Lookup(PPointPair(loophead, source)));

      if (!body_table->Insert(PPointPair(loophead, source))) {
        body_list->PushBack(source);
        worklist.PushBack(source);
      }
    }
  }

  // this should only be called on loops that have actual backedges
  Assert(!worklist.Empty());

  while (!worklist.Empty()) {
    PPoint back = worklist.Back();
    worklist.PopBack();

    if (back == loophead)
      continue;

    const Vector<PEdge*> &incoming = cfg->GetIncomingEdges(back);
    for (size_t iind = 0; iind < incoming.Size(); iind++) {
      PEdge *edge = incoming[iind];
      PPoint source = edge->GetSource();

      if (reach_table->Lookup(PPointPair(loophead, source))) {
        if (!body_table->Insert(PPointPair(loophead, source))) {
          body_list->PushBack(source);
          worklist.PushBack(source);
        }
      }
      else if (entry_reach_table->Lookup(source)) {
        // the source is not reachable from the loophead.
        // this is an irreducible edge.
        irreducible_edges->PushBack(edge);
      }
    }
  }
}

// clone a loop body, mapping each point in the body of loophead
// to a new point in receive_cfg. receive_cfg will receive new points
// for the cloned body, and new edges for any non-backedge whose source
// and target are both in loophead's body. for other edges involving loophead,
// old_entry/exit/backedge_indexes will be filled in with indexes into
// the edges list of base_cfg. it may be that base_cfg == receive_cfg.
void CloneLoopBody(BlockCFG *base_cfg, PPoint loophead,
                   PPointListHash *remapping,
                   BlockCFG *receive_cfg,
                   Vector<size_t> *old_entry_indexes,
                   Vector<size_t> *old_exit_indexes,
                   Vector<size_t> *old_back_indexes)
{
  Assert(remapping->IsEmpty());

  Vector<PPoint> *body_list = body_list_table->Lookup(loophead, true);
  Assert(!body_list->Empty());

  // allow for base_cfg == receive_cfg, so keep track of how many points and
  // edges were originally in base_cfg before modifying receive_cfg.
  size_t init_points_size = base_cfg->GetPointCount();
  size_t init_edges_size = base_cfg->GetEdgeCount();

  // copy all points in the loop body to the new CFG.
  for (size_t bind = 0; bind < body_list->Size(); bind++) {
    PPoint body_point = body_list->At(bind);
    Assert(remapping->Lookup(body_point, false) == NULL);

    Assert(0 < body_point && body_point <= init_points_size);
    Location *loc = base_cfg->GetPointLocation(body_point);

    PPoint new_point = receive_cfg->AddPoint(loc);
    remapping->Insert(body_point, new_point);
  }

  // copy all edges between points in the body to the new CFG.
  for (size_t eind = 0; eind < init_edges_size; eind++) {
    PEdge *edge = base_cfg->GetEdge(eind);
    PPoint source = edge->GetSource();
    PPoint target = edge->GetTarget();

    if (!entry_reach_table->Lookup(source))
      continue;

    PPoint new_source = 0;
    if (body_table->Lookup(PPointPair(loophead, source)))
      new_source = remapping->LookupSingle(source);

    PPoint new_target = 0;
    if (body_table->Lookup(PPointPair(loophead, target)))
      new_target = remapping->LookupSingle(target);

    if (!new_source && !new_target) {
      // edge is not involved with this loop. leave it alone
    }
    else if (!new_source && new_target) {
      // entry edge. leave it alone
      old_entry_indexes->PushBack(eind);
    }
    else if (new_source && !new_target) {
      // exit edge. leave it alone
      old_exit_indexes->PushBack(eind);
    }
    else {
      Assert(new_source && new_target);

      if (target == loophead) {
        // back edge. leave it alone
        Assert(backedge_table->Lookup(edge));
        old_back_indexes->PushBack(eind);
      }
      else {
        // inner edge. clone the edge for the new source and target
        PEdge *new_edge = PEdge::ChangeEdge(edge, new_source, new_target);
        receive_cfg->AddEdge(new_edge);
      }
    }
  }
}

// get the result of transitively following skip edges from point
PPoint FollowSkipEdges(BlockCFG *cfg, PPoint point)
{
  PPoint cur = point;
  bool changed = true;

  while (changed) {
    changed = false;

    const Vector<PEdge*> &outgoing = cfg->GetOutgoingEdges(cur);
    if (outgoing.Size() == 1) {
      PEdge *edge = outgoing[0];
      if (edge->IsSkip()) {
        PPoint next = edge->GetTarget();

        // watch out for skip edges aborting the function.
        if (next) {
          cur = next;
          changed = true;
        }
      }
    }
  }

  return cur;
}

void CopyCFGLocationsVariables(BlockCFG *old_cfg, BlockCFG *new_cfg)
{
  String *command = old_cfg->GetCommand();
  if (command)
    new_cfg->SetCommand(command);

  Location *begin_loc = old_cfg->GetBeginLocation();
  new_cfg->SetBeginLocation(begin_loc);

  Location *end_loc = old_cfg->GetEndLocation();
  new_cfg->SetEndLocation(end_loc);

  const Vector<DefineVariable> *variables = old_cfg->GetVariables();
  if (variables) {
    for (size_t vind = 0; vind < variables->Size(); vind++) {
      const DefineVariable &dv = variables->At(vind);
      new_cfg->AddVariable(dv.var, dv.type);
    }
  }
}

void CopyCFGPointsEdges(BlockCFG *old_cfg, BlockCFG *new_cfg)
{
  // duplicate the CFG's points list.
  for (size_t pind = 0; pind < old_cfg->GetPointCount(); pind++) {
    Location *loc = old_cfg->GetPointLocation(pind + 1);
    new_cfg->AddPoint(loc);
  }

  // set the entry/exit points.
  new_cfg->SetEntryPoint(old_cfg->GetEntryPoint());
  new_cfg->SetExitPoint(old_cfg->GetExitPoint());

  // duplicate the CFG's loop heads list.
  for (size_t lind = 0; lind < old_cfg->GetLoopHeadCount(); lind++) {
    const LoopHead &head = old_cfg->GetLoopHead(lind);
    new_cfg->AddLoopHead(head.point, head.end_location);
  }

  // duplicate the CFG's edges list.
  for (size_t eind = 0; eind < old_cfg->GetEdgeCount(); eind++) {
    PEdge *edge = old_cfg->GetEdge(eind);
    new_cfg->AddEdge(edge);
  }
}

void TrimUnreachable(BlockCFG *cfg, bool flatten_skips)
{
  // can't flatten skips if there might be loops in the CFG.
  Assert(!flatten_skips || cfg->GetLoopHeadCount() == 0);

  // receives the locations of the new points and edges of the CFG. we will
  // fill these in, then replace wholesale the old points/edges on the CFG.
  Vector<Location*> new_points;
  Vector<PEdge*> new_edges;
  Vector<LoopHead> new_loop_heads;

  Vector<PPoint> worklist;

  // get the set of points reachable from CFG entry.
  // worklist items are points in entry_reachable whose outgoing edges
  // have not been examined.
  PPointHash entry_reachable;

  PPoint entry = cfg->GetEntryPoint();
  entry_reachable.Insert(entry);
  worklist.PushBack(entry);

  while (!worklist.Empty()) {
    PPoint back = worklist.Back();
    worklist.PopBack();

    const Vector<PEdge*> &outgoing = cfg->GetOutgoingEdges(back);
    for (size_t oind = 0; oind < outgoing.Size(); oind++) {
      PEdge *edge = outgoing[oind];
      PPoint next = edge->GetTarget();

      if (!entry_reachable.Lookup(next)) {
        entry_reachable.Insert(next);
        worklist.PushBack(next);
      }
    }
  }

  // get the set of points which reach the CFG exit.
  // worklist items are points in exit_reaches whose incoming edges
  // have not been examined.
  PPointHash exit_reaches;

  PPoint exit = cfg->GetExitPoint();
  exit_reaches.Insert(exit);
  worklist.PushBack(exit);

  while (!worklist.Empty()) {
    PPoint back = worklist.Back();
    worklist.PopBack();

    const Vector<PEdge*> &incoming = cfg->GetIncomingEdges(back);
    for (size_t iind = 0; iind < incoming.Size(); iind++) {
      PEdge *edge = incoming[iind];
      PPoint prev = edge->GetSource();

      if (!exit_reaches.Lookup(prev)) {
        exit_reaches.Insert(prev);
        worklist.PushBack(prev);
      }
    }
  }

  // make sure we include the entry regardless of whether the function
  // has a path from entry to exit.
  exit_reaches.Insert(entry);
  if (flatten_skips)
    exit_reaches.Insert(FollowSkipEdges(cfg, entry));

  // map from old points to corresponding new points. only defined for
  // points that are in both entry_reachable and exit_reaches,
  // and that do not have outgoing skip edges (if flatten_skips is set).
  PPointListHash remapping;

  // map from some old p0 to another old p1 where p0 connects to p1 by
  // skip edges and p1 has no outgoing skips. empty if flatten_skips is
  // not set. only defined if remapping is defined for p1.
  PPointListHash skip_remapping;

  for (PPoint point = 1; point <= cfg->GetPointCount(); point++) {
    if (entry_reachable.Lookup(point) && exit_reaches.Lookup(point)) {

      // if this is just the source of some skip edges flatten them out.
      // the target of the skips will be defined by remapping since
      // there can be only one outgoing skip edge from a point and
      // thus all paths from point pass through target_point; if point
      // reaches the exit then so does target_point.
      if (flatten_skips) {
        PPoint target_point = FollowSkipEdges(cfg, point);
        if (target_point != point) {
          skip_remapping.Insert(point, target_point);

          // don't add anything to remapping for point
          continue;
        }
      }

      Location *loc = cfg->GetPointLocation(point);
      new_points.PushBack(loc);
      PPoint new_point = new_points.Size();

      remapping.Insert(point, new_point);
    }
  }

  for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
    PEdge *edge = cfg->GetEdge(eind);

    PPoint source = edge->GetSource();
    PPoint target = edge->GetTarget();

    if (skip_remapping.Lookup(source, false))
      continue;

    // flatten any skips after the target point
    Vector<PPoint> *skip_target_list = skip_remapping.Lookup(target, false);
    if (skip_target_list) {
      Assert(skip_target_list->Size() == 1);
      target = skip_target_list->At(0);
    }

    Vector<PPoint> *new_source_list = remapping.Lookup(source, false);
    Vector<PPoint> *new_target_list = remapping.Lookup(target, false);

    if (new_source_list && new_target_list) {
      Assert(new_source_list->Size() == 1);
      Assert(new_target_list->Size() == 1);

      PPoint new_source = new_source_list->At(0);
      PPoint new_target = new_target_list->At(0);

      PEdge *new_edge = PEdge::ChangeEdge(edge, new_source, new_target);
      new_edges.PushBack(new_edge);
    }
  }

  for (size_t lind = 0; lind < cfg->GetLoopHeadCount(); lind++) {
    const LoopHead &head = cfg->GetLoopHead(lind);

    // don't check skip_remapping because we don't allow skip flattening
    // when the CFG still has loops in it

    Vector<PPoint> *new_point_list = remapping.Lookup(head.point, false);
    if (new_point_list) {
      Assert(new_point_list->Size() == 1);
      LoopHead new_head(new_point_list->At(0), head.end_location);
      new_loop_heads.PushBack(new_head);
    }
  }

  // clear out the initial CFG.
  cfg->ClearBody();

  // add the new points, edges, loop heads.
  for (size_t pind = 0; pind < new_points.Size(); pind++)
    cfg->AddPoint(new_points[pind]);
  for (size_t eind = 0; eind < new_edges.Size(); eind++)
    cfg->AddEdge(new_edges[eind]);
  for (size_t lind = 0; lind < new_loop_heads.Size(); lind++)
    cfg->AddLoopHead(new_loop_heads[lind].point,
                     new_loop_heads[lind].end_location);

  // set the new entry and exit points of the CFG.

  // the entry may be connected to skip edges
  Vector<PPoint> *skip_entry_list = skip_remapping.Lookup(entry, false);
  if (skip_entry_list) {
    Assert(skip_entry_list->Size() == 1);
    entry = skip_entry_list->At(0);
  }

  PPoint new_entry = remapping.LookupSingle(entry);
  PPoint new_exit = 0;

  Vector<PPoint> *new_exit_list = remapping.Lookup(exit, false);
  if (new_exit_list) {
    Assert(new_exit_list->Size() == 1);
    new_exit = new_exit_list->At(0);
  }

  cfg->SetEntryPoint(new_entry);
  cfg->SetExitPoint(new_exit);
}

void TopoSortCFG(BlockCFG *cfg)
{
  // can't topo sort a CFG that might have loops.
  Assert(cfg->GetLoopHeadCount() == 0);

  // map from old CFG points to the new points in the topo order. we can only
  // add a new point once we've added all its predecessors.
  PPointListHash remapping;

  // points in the remappping, in the order to add them to the CFG.
  Vector<Location*> new_points;

  // map from new points back to original CFG points.
  Vector<PPoint> old_points;

  // worklist items are the points where the sources of incoming edges have
  // already been added to the remapping, the point itself has not.
  Vector<PPoint> worklist;

  PPoint entry_point = cfg->GetEntryPoint();
  PPoint exit_point = cfg->GetExitPoint();

  // seed the worklist.
  worklist.PushBack(entry_point);

  while (!worklist.Empty()) {
    // pick the point from the worklist with the minimum line number.
    // if there is code like:
    //   if (x)
    //     a;
    //   else
    //     b;
    // we could add either a or b to the remapping first, but we want to add
    // a first. the ordering of points is used for naming loops, and we want
    // this ordering to be deterministic and map back to the code predictably.

    size_t best_index = 0;
    size_t best_line = cfg->GetPointLocation(worklist[0])->Line();

    for (size_t ind = 1; ind < worklist.Size(); ind++) {
      size_t new_line = cfg->GetPointLocation(worklist[ind])->Line();
      if (new_line < best_line) {
        best_index = ind;
        best_line = new_line;
      }
    }

    PPoint point = worklist[best_index];
    worklist[best_index] = worklist.Back();
    worklist.PopBack();

    Assert(!remapping.Lookup(point, false));

    Location *loc = cfg->GetPointLocation(point);
    new_points.PushBack(loc);
    old_points.PushBack(point);

    remapping.Insert(point, new_points.Size());

    const Vector<PEdge*> &outgoing = cfg->GetOutgoingEdges(point);
    for (size_t oind = 0; oind < outgoing.Size(); oind++) {
      PEdge *edge = outgoing[oind];
      PPoint target = edge->GetTarget();

      // this can happen if there are multiple edges from the worklist point
      // to the target, e.g. 'if (x) {}'. not going to happen much.
      if (worklist.Contains(target))
        continue;

      Assert(!remapping.Lookup(target, false));

      // we can add the target to the worklist if it has no incoming edges
      // from points not in the remapping.
      bool missing_incoming = false;

      const Vector<PEdge*> &incoming = cfg->GetIncomingEdges(target);
      for (size_t iind = 0; iind < incoming.Size(); iind++) {
        PEdge *edge = incoming[iind];
        PPoint source = edge->GetSource();
        if (!remapping.Lookup(source, false)) {
          missing_incoming = true;
          break;
        }
      }

      if (!missing_incoming)
        worklist.PushBack(target);
    }
  }

  // this assert will fail if either the CFG contains cycles, or if there are
  // nodes unreachable from the start. neither of these cases should be
  // possible here.
  Assert(new_points.Size() == cfg->GetPointCount());
  Assert(old_points.Size() == cfg->GetPointCount());

  // remap all the edges. this is also done so that the edges will be
  // in topological order according to their source points.
  Vector<PEdge*> new_edges;

  for (size_t pind = 0; pind < old_points.Size(); pind++) {
    const Vector<PEdge*> &edges = cfg->GetOutgoingEdges(old_points[pind]);

    for (size_t eind = 0; eind < edges.Size(); eind++) {
      PEdge *edge = edges[eind];

      PPoint new_source = remapping.LookupSingle(edge->GetSource());
      PPoint new_target = remapping.LookupSingle(edge->GetTarget());

      PEdge *new_edge = PEdge::ChangeEdge(edge, new_source, new_target);
      new_edges.PushBack(new_edge);
    }
  }

  // clear out the initial CFG.
  cfg->ClearBody();

  // add the new points, edges, annotations.
  for (size_t pind = 0; pind < new_points.Size(); pind++)
    cfg->AddPoint(new_points[pind]);
  for (size_t eind = 0; eind < new_edges.Size(); eind++)
    cfg->AddEdge(new_edges[eind]);

  // set the new entry point. this had better be the first point in the order.
  PPoint new_entry_point = remapping.LookupSingle(entry_point);
  Assert(new_entry_point == 1);
  cfg->SetEntryPoint(new_entry_point);

  if (exit_point) {
    // set the new exit point. this had better be the last point in the order.
    PPoint new_exit_point = remapping.LookupSingle(exit_point);
    Assert(new_exit_point == new_points.Size());
    cfg->SetExitPoint(new_exit_point);
  }
}

// remove the irreducible entry edges on loophead by cloning the body
// of loophead, redirecting the irreducible edges to that cloned body,
// and directing the back edges of the cloned loop back to the entry
// of the real loop. destructively modifies cfg.
void ReduceLoop(BlockCFG *cfg, PPoint loophead,
                const Vector<PEdge*> &irreducible_edges)
{
  PPointListHash remapping;

  Vector<size_t> old_entry_indexes;
  Vector<size_t> old_exit_indexes;
  Vector<size_t> old_back_indexes;

  CloneLoopBody(cfg, loophead, &remapping, cfg,
                &old_entry_indexes, &old_exit_indexes, &old_back_indexes);

  // replace the irreducible entry edges with edges into the
  // corresponding point in the new loop.
  for (size_t iind = 0; iind < irreducible_edges.Size(); iind++) {
    PEdge *irr_edge = irreducible_edges[iind];
    bool found_index = false;

    for (size_t oind = 0; oind < old_entry_indexes.Size(); oind++) {
      size_t entry_index = old_entry_indexes[oind];
      PEdge *old_edge = cfg->GetEdge(entry_index);

      if (old_edge == irr_edge) {
        Assert(!found_index);
        found_index = true;

        PPoint source = old_edge->GetSource();
        PPoint target = old_edge->GetTarget();
        PPoint new_target = remapping.LookupSingle(target);

        PEdge *new_edge = PEdge::ChangeEdge(old_edge, source, new_target);
        cfg->SetEdge(entry_index, new_edge);
      }
    }

    Assert(found_index);
  }

  // add the old exit edges for the new loop.
  for (size_t oind = 0; oind < old_exit_indexes.Size(); oind++) {
    PEdge *old_edge = cfg->GetEdge(old_exit_indexes[oind]);

    PPoint source = old_edge->GetSource();
    PPoint target = old_edge->GetTarget();
    PPoint new_source = remapping.LookupSingle(source);

    PEdge *new_edge = PEdge::ChangeEdge(old_edge, new_source, target);
    cfg->AddEdge(new_edge);
  }

  // add the old back edges as edges to the entry point of the old loop.
  for (size_t oind = 0; oind < old_back_indexes.Size(); oind++) {
    PEdge *old_edge = cfg->GetEdge(old_back_indexes[oind]);

    PPoint source = old_edge->GetSource();
    PPoint target = old_edge->GetTarget();
    PPoint new_source = remapping.LookupSingle(source);

    Assert(target == loophead);

    PEdge *new_edge = PEdge::ChangeEdge(old_edge, new_source, target);
    cfg->AddEdge(new_edge);
  }

  // add any loopheads that may have been duplicated within the cloned loop.
  // note that the new loophead does not have any incoming edges and will
  // get trimmed by TrimUnreachable().
  for (size_t lind = 0; lind < cfg->GetLoopHeadCount(); lind++) {
    const LoopHead &head = cfg->GetLoopHead(lind);

    Vector<PPoint> *new_point_list = remapping.Lookup(head.point, false);
    if (new_point_list) {
      Assert(new_point_list->Size() == 1);
      LoopHead new_head(new_point_list->At(0), head.end_location);
      cfg->AddLoopHead(new_head.point, new_head.end_location);
    }
  }

  // trim unreachable portions of the cfg, but do not collapse skip edges.
  TrimUnreachable(cfg, false);
}

// split a single loop from the existing body. this creates a new CFG
// with cloned points and edges for the loop's execution, and fixes up
// the points and edges in base_cfg to add a Loop() summary edge and remove
// the CFG cycle.
BlockCFG* SplitSingleLoop(PPoint loophead, const Vector<PPoint> &all_loops,
                          BlockCFG *base_cfg)
{
  // make a temporary name for the loop.
  char loop_name[100];
  snprintf(loop_name, sizeof(loop_name), "scratch#%d", loophead);

  Variable *function_info = base_cfg->GetId()->BaseVar();

  // make an ID for the split loop.
  String *loop_info = String::Make(loop_name);
  BlockId *loop_id = BlockId::Make(B_Loop, function_info, loop_info);

  // make a CFG for the split loop.
  BlockCFG *loop_cfg = BlockCFG::Make(loop_id);
  CopyCFGLocationsVariables(base_cfg, loop_cfg);

  PPointListHash remapping;
  Vector<size_t> old_entry_indexes;
  Vector<size_t> old_exit_indexes;
  Vector<size_t> old_back_indexes;

  CloneLoopBody(base_cfg, loophead, &remapping, loop_cfg,
                &old_entry_indexes, &old_exit_indexes, &old_back_indexes);

  // fixup the old CFG first. we need to perform the following steps:
  // - create a new point with a Loop() edge going to the head.
  // - add the new point to the body of any loop also containing the head.
  // - change all loop entry edges to go to the new point instead of the head.
  // - delete all backedges on the loop by pointing them to point 0.

  Location *loop_head_loc = base_cfg->GetPointLocation(loophead);

  PPoint summary_point = base_cfg->AddPoint(loop_head_loc);
  PEdge *summary_edge = PEdge::MakeLoop(summary_point, loophead, loop_id);
  base_cfg->AddEdge(summary_edge);

  // mark the new summary point as being reachable from the entry point.
  entry_reach_table->Insert(summary_point);

  // add the new summary point to the body of any other loop which
  // already contains the head of this loop in its body.
  for (size_t lind = 0; lind < all_loops.Size(); lind++) {
    if (body_table->Lookup(PPointPair(all_loops[lind], loophead))) {
      body_table->Insert(PPointPair(all_loops[lind], summary_point));
      body_list_table->Insert(all_loops[lind], summary_point);
    }
  }

  for (size_t oind = 0; oind < old_entry_indexes.Size(); oind++) {
    size_t entry_index = old_entry_indexes[oind];
    PEdge *old_edge = base_cfg->GetEdge(entry_index);

    PPoint source = old_edge->GetSource();
    Assert(old_edge->GetTarget() == loophead);

    PEdge *new_edge = PEdge::ChangeEdge(old_edge, source, summary_point);
    base_cfg->SetEdge(entry_index, new_edge);
  }

  for (size_t oind = 0; oind < old_back_indexes.Size(); oind++) {
    size_t back_index = old_back_indexes[oind];
    PEdge *old_edge = base_cfg->GetEdge(back_index);

    PPoint source = old_edge->GetSource();
    Assert(old_edge->GetTarget() == loophead);

    PEdge *new_edge = PEdge::ChangeEdge(old_edge, source, 0);
    base_cfg->SetEdge(back_index, new_edge);
  }

  // fixup the new CFG second. we need to perform the following steps:
  // - mark the cloned head as the entry point.
  // - create a new point as the exit point.
  // - for each backedge in the original loop, redirect to the exit point.

  PPoint split_entry = remapping.LookupSingle(loophead);

  // find the exit location associated with this loop head, if there is one.
  size_t headind = 0;
  for (; headind < base_cfg->GetLoopHeadCount(); headind++) {
    if (base_cfg->GetLoopHead(headind).point == loophead)
      break;
  }
  Assert(headind < base_cfg->GetLoopHeadCount());
  Location *end_location = base_cfg->GetLoopHead(headind).end_location;

  // if there isn't an end location (goto loop in the original source),
  // just use the location of the loop head itself.
  if (!end_location)
    end_location = loop_head_loc;

  PPoint split_exit = loop_cfg->AddPoint(end_location);

  for (size_t oind = 0; oind < old_back_indexes.Size(); oind++) {
    size_t back_index = old_back_indexes[oind];
    PEdge *old_edge = base_cfg->GetEdge(back_index);

    PPoint source = old_edge->GetSource();

    // we should have already dropped the target of this edge.
    Assert(old_edge->GetTarget() == 0);

    PPoint new_source = remapping.LookupSingle(source);
    PEdge *new_edge = PEdge::ChangeEdge(old_edge, new_source, split_exit);
    loop_cfg->AddEdge(new_edge);
  }

  // set the entry/exit points of the loop CFG.
  loop_cfg->SetEntryPoint(split_entry);
  loop_cfg->SetExitPoint(split_exit);

  // trim any unreachable portions of the loop CFG, collapse skips
  // and sort the points.
  TrimUnreachable(loop_cfg, true);
  TopoSortCFG(loop_cfg);

  // set the end location of the loop to the point in the body with the
  // highest line number. the GCC frontend does not have information
  // about the end location of loop bodies.
  Location *highest = end_location;
  for (PPoint point = 1; point <= loop_cfg->GetPointCount(); point++) {
    Location *loc = loop_cfg->GetPointLocation(point);
    if (loc->FileName() == highest->FileName() && loc->Line() > highest->Line())
      highest = loc;
  }
  loop_cfg->SetPointLocation(loop_cfg->GetExitPoint(), highest);

  return loop_cfg;
}

// marks the points in cfg which are isomorphic to points in the loop_cfg
// invoked by cfg at the specified edge. code in a syntactic loop body
// will be reflected in CFGs for both the loop and its parent if it may
// reach both the recursive loop edge and a loop exit point. this common
// code will be isomorphic between the two CFGs.
void GetLoopIsomorphicPoints(BlockCFG *cfg, PEdge *loop_edge,
                             BlockCFG *loop_cfg)
{
  // mapping from points in cfg to isomorphic points in loop_cfg.
  PPointListHash remapping;

  // worklist items are isomorphic points whose outgoing edges have not
  // been examined.
  Vector<PPoint> worklist;

  PPoint target = loop_edge->GetTarget();
  remapping.Insert(target, loop_cfg->GetEntryPoint());
  cfg->AddLoopIsomorphic(target);
  worklist.PushBack(target);

  while (!worklist.Empty()) {
    PPoint cfg_point = worklist.Back();
    worklist.PopBack();

    PPoint loop_point = remapping.LookupSingle(cfg_point);

    const Vector<PEdge*> &cfg_outgoing =
      cfg->GetOutgoingEdges(cfg_point);
    const Vector<PEdge*> &loop_outgoing =
      loop_cfg->GetOutgoingEdges(loop_point);

    for (size_t eind = 0; eind < cfg_outgoing.Size(); eind++) {
      PEdge *edge = cfg_outgoing[eind];
      PPoint target = edge->GetTarget();

      // check for an existing remapping entry. some isomorphic points have
      // multiple incoming edges. we don't need to check all such incoming
      // edges; if any edge is isomorphic, they all will be.
      if (remapping.Lookup(target, false))
        continue;

      // look for an equivalent outgoing edge from the loop.
      PPoint loop_target = 0;

      for (size_t lind = 0; lind < loop_outgoing.Size(); lind++) {
        PEdge *loop_edge = loop_outgoing[lind];

        if (PEdge::CompareInner(edge, loop_edge) == 0) {
          loop_target = loop_edge->GetTarget();
          break;
        }
      }

      if (!loop_target) {
        Assert(edge->IsAssume());
        continue;
      }

      remapping.Insert(target, loop_target);
      cfg->AddLoopIsomorphic(target);
      worklist.PushBack(target);
    }
  }
}

// assign the final names to all loops within cfg. loop naming is done after
// the CFGs have been finalized as it depends on the topo ordering of points.
static void FillLoopNames(BlockCFG *cfg, const char *prefix,
                          const Vector<BlockCFG*> &cfg_list)
{
  size_t found_loops = 0;

  for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
    PEdgeLoop *edge = cfg->GetEdge(eind)->IfLoop();
    if (!edge)
      continue;

    BlockId *loop = edge->GetLoopId();

    // check for a duplicate. there can be multiple summary edges for
    // a loop if we reduced some irreducible loops or if there are
    // isomorphic points in the outer body of a nested loop.
    if (loop->WriteLoop() != NULL)
      continue;

    char name_buf[100];
    snprintf(name_buf, sizeof(name_buf), "%s#%d", prefix, (int) found_loops);
    String *write_name = String::Make(name_buf);
    loop->SetWriteLoop(write_name);

    found_loops++;

    // recurse on the CFG for the loop itself, to get any nested loops.
    bool found = false;
    for (size_t ind = 0; ind < cfg_list.Size(); ind++) {
      if (cfg_list[ind]->GetId() == loop) {
        Assert(!found);
        found = true;
        FillLoopNames(cfg_list[ind], name_buf, cfg_list);
      }
    }
    Assert(found);
  }
}

void SplitLoops(BlockCFG *base_cfg, Vector<BlockCFG*> *result_cfg_list)
{
  // get the CFG which will eventually become the loop-free outer function CFG.
  BlockCFG *func_cfg;
  if (base_cfg->GetId()->Kind() == B_FunctionWhole) {
    // make an ID for the outer function body.
    Variable *function_info = base_cfg->GetId()->BaseVar();
    BlockId *outer_id = BlockId::Make(B_Function, function_info);

    // make the function CFG by cloning the base CFG with the new ID.
    func_cfg = BlockCFG::Make(outer_id);
    CopyCFGLocationsVariables(base_cfg, func_cfg);
    CopyCFGPointsEdges(base_cfg, func_cfg);
  }
  else if (base_cfg->GetId()->Kind() == B_Function) {
    // this call came from a recursive invocation of SplitLoops after we
    // removed an irreducible loop from the function.
    func_cfg = base_cfg;
  }
  else {
    // just destructively update the original CFG.
    func_cfg = base_cfg;
  }

  // add a new entry point with a skip edge to the original entry point.
  // loop splitting breaks if the entry point is marked as a loop head.

  PPoint entry = func_cfg->GetEntryPoint();
  Location *loc = func_cfg->GetPointLocation(entry);
  PPoint new_entry = func_cfg->AddPoint(loc);

  PEdge *skip_edge = PEdge::MakeSkip(new_entry, entry);
  func_cfg->AddEdge(skip_edge);
  func_cfg->SetEntryPoint(new_entry);

  // setup the tables we need to do loop splitting.
  SetupTables();

  // compute the points reachable from the entry point.
  GetEntryReachable(func_cfg);

  // the real loops in the program with back edges.
  Vector<PPoint> loops;

  for (size_t lind = 0; lind < func_cfg->GetLoopHeadCount(); lind++) {
    PPoint head = func_cfg->GetLoopHead(lind).point;
    if (GetLoopBackedges(func_cfg, head))
      loops.PushBack(head);
  }

  // compute reachability and check for irreducible loops.
  for (size_t lind = 0; lind < func_cfg->GetLoopHeadCount(); lind++) {
    const LoopHead &head = func_cfg->GetLoopHead(lind);

    if (GetLoopReachable(func_cfg, head.point)) {
      // loop is irreducible.

      // get the loop's irreducible edges.
      Vector<PEdge*> irreducible_edges;
      GetLoopBody(func_cfg, head.point, &irreducible_edges);
      Assert(!irreducible_edges.Empty());

      // clone the loop's body and remove the irreducible edges.
      ReduceLoop(func_cfg, head.point, irreducible_edges);

      // try again on the modified CFG.
      CleanupTables();
      SplitLoops(func_cfg, result_cfg_list);
      return;
    }
  }

  // there are no irreducible loops at this point so this should
  // never have any entries added.
  Vector<PEdge*> irreducible_edges;

  // compute loop bodies.
  for (size_t lind = 0; lind < loops.Size(); lind++) {
    PPoint head = loops[lind];
    GetLoopBody(func_cfg, head, &irreducible_edges);
    Assert(irreducible_edges.Empty());
  }

  // construct a tree of all the loops. loop A contains loop B
  // if A != B and the head of B is in the body of A.
  PPointListHash loop_tree;

  // split off all the loops in the CFG. make sure we split inner loops
  // before outer, so that the Loop edges on inner loops will appear in
  // the split body for outer loops.
  while (!loops.Empty()) {

    // find a candidate loop to split. this is one whose loop children
    // have already been split off and are no longer in the loops list.
    PPoint loophead = 0;
    for (size_t lind = 0; lind < loops.Size(); lind++) {

      bool is_viable = true;
      for (size_t xlind = 0; xlind < loops.Size(); xlind++) {
        if (xlind == lind)
          continue;
        Assert(loops[lind] != loops[xlind]);

        if (body_table->Lookup(PPointPair(loops[lind], loops[xlind]))) {
          is_viable = false;
          break;
        }
      }

      if (is_viable) {
        loophead = loops[lind];
        loops[lind] = loops.Back();
        loops.PopBack();
        break;
      }
    }

    Assert(loophead);
    BlockCFG *loop_cfg = SplitSingleLoop(loophead, loops, func_cfg);
    result_cfg_list->PushBack(loop_cfg);
  }

  // clear out the loopheads, we don't want them around anymore.
  func_cfg->ClearLoopHeads();

  // trim unreachable points in the function CFG (i.e. bodies of loops that
  // now redirect to point zero), collapse skips and topo sort.
  TrimUnreachable(func_cfg, true);
  TopoSortCFG(func_cfg);

  result_cfg_list->PushBack(func_cfg);
  CleanupTables();

  // fill in any loop parents for the inner loop CFGs, and make sure the
  // result CFGs are ordered correctly, with inner loops before outer loops
  // and the outer function.
  for (size_t cind = 0; cind < result_cfg_list->Size(); cind++) {
    BlockCFG *cfg = result_cfg_list->At(cind);

    for (size_t eind = 0; eind < cfg->GetEdgeCount(); eind++) {
      if (PEdgeLoop *edge = cfg->GetEdge(eind)->IfLoop()) {
        BlockId *target_id = edge->GetLoopId();

        bool found_target = false;
        for (size_t xcind = 0; xcind < cind; xcind++) {
          BlockCFG *xcfg = result_cfg_list->At(xcind);
          if (xcfg->GetId() == target_id) {
            found_target = true;

            BlockPPoint where(cfg->GetId(), edge->GetSource());
            xcfg->AddLoopParent(where);

            // mark the isomorphic points in the parent CFG.
            GetLoopIsomorphicPoints(cfg, edge, xcfg);

            break;
          }
        }

        Assert(found_target);
      }
    }
  }

  // assign the final names to the various loop CFGs.
  FillLoopNames(func_cfg, "loop", *result_cfg_list);
}

NAMESPACE_XGILL_END
