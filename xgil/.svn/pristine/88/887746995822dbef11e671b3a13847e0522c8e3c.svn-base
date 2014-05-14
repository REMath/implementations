
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

// data structures and functions for escape analysis.

#include <imlang/block.h>
#include <imlang/trace.h>

NAMESPACE_XGILL_BEGIN

extern ConfigOption print_escape;

// store the target of an escape edge to some trace location.
struct EscapeEdge
{
  // target trace location of the edge.
  Trace *target;

  // point in the program where the escape edge occurs. this is versioned.
  BlockPPoint where;

  // whether this edge moves data from a callee to caller, or vice versa.
  // at most of one of these will be set. if one is set, 'where' indicates
  // the call site the movement occurs at.
  bool move_caller;
  bool move_callee;

  EscapeEdge() : target(NULL) {}
  EscapeEdge(Trace *_target, BlockPPoint _where,
             bool _move_caller, bool _move_callee)
    : target(_target), where(_where),
      move_caller(_move_caller), move_callee(_move_callee)
  {}

  bool operator == (const EscapeEdge &o) const {
    return target == o.target &&
      move_caller == o.move_caller && move_callee == o.move_callee &&
      BlockPPoint::Similar(where, o.where);
  }

  void Print(OutStream &out) const
  {
    out << target
        << (move_caller ? " [move_caller]" : "")
        << (move_callee ? " [move_callee]" : "")
        << " [" << where << "]";
  }
};

// set of forward or backward edges from one trace location to another.
// if there is an assign 'x := y', then there will be a forward set for
// *y containing *x, and a backward set for *x containing *y.
class EscapeEdgeSet : public HashObject
{
 public:
  static int Compare(const EscapeEdgeSet *eset0, const EscapeEdgeSet *eset1);
  static EscapeEdgeSet* Copy(const EscapeEdgeSet *eset);
  static void Write(Buffer *buf, const EscapeEdgeSet *eset);
  static EscapeEdgeSet* Read(Buffer *buf);

  static void WriteList(Buffer *buf, const Vector<EscapeEdgeSet*> &eset_list);
  static void ReadList(Buffer *buf, Vector<EscapeEdgeSet*> *eset_list);

  static void WriteMerge(Buffer *buf, Trace *source, bool forward,
                         const Vector<EscapeEdge> &edges);
  static void ReadMerge(Buffer *buf, Trace **psource, bool *pforward,
                        Vector<EscapeEdge> *pedges);

  static EscapeEdgeSet* Make(Trace *source, bool forward) {
    EscapeEdgeSet xeset(source, forward);
    return g_table.Lookup(xeset);
  }

 public:
  // get the source of all the edges in this set.
  Trace* GetSource() const { return m_source; }

  // whether the edges in this set are forward or backward.
  bool IsForward() const { return m_forward; }

  // get the edges from the source of this set.
  size_t GetEdgeCount() const;
  const EscapeEdge& GetEdge(size_t ind) const;

  // add an edge at the specified point to target.
  void AddEdge(const EscapeEdge &edge);

  // set the version for the location of a particular edge.
  void SetEdgeVersion(size_t ind, VersionId version);

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  Trace *m_source;
  bool m_forward;

  // all known escape edges for the source.
  Vector<EscapeEdge> *m_edges;

  EscapeEdgeSet(Trace *source, bool forward);
  static HashCons<EscapeEdgeSet> g_table;
};

// kinds of ways in which a trace can be accessed.
enum EscapeAccessKind {
  EAK_Invalid = 0,

  // trace is read from. its value Drf(T) is copied somewhere else, or it is
  // used in a branch, as the target of an indirect call, and so forth.
  EAK_Read = 1,

  // trace is written from. its value Drf(T) is replaced with something else.
  EAK_Write = 2,

  // trace has some array index Index(T,...) taken.
  EAK_Index = 3,

  // trace has a field Fld(T,F) accessed. 
  EAK_Fld = 4,

  // trace has its reverse field Rfld(T,F) taken.
  EAK_Rfld = 5
};

// information on a single access to some trace location.
struct EscapeAccess
{
  // kind of access this is.
  EscapeAccessKind kind;

  // the trace location being accessed.
  Trace *target;

  // point in the program where the access occurs. this is versioned.
  BlockPPoint where;

  // field for EAK_Fld and EAK_Rfld accesses.
  Field *field;

  EscapeAccess() : kind(EAK_Invalid), target(NULL), field(NULL) {}
  EscapeAccess(EscapeAccessKind _kind, Trace *_target,
               BlockPPoint _where, Field *_field)
    : kind(_kind), target(_target), where(_where), field(_field) {}

  bool operator == (const EscapeAccess &o) const {
    return kind == o.kind && target == o.target && field == o.field &&
      BlockPPoint::Similar(where, o.where);
  }
};

// set of accesses to a particular trace location at different
// points in the program. each use of a trace in the program can
// create multiple accesses. for example, an assignment 'x->f := y'
// constitutes read accesses on x and y, a field access on *x,
// and write accesses on x->f and .f (the trace location for all
// uses of field f).
class EscapeAccessSet : public HashObject
{
 public:
  static int Compare(const EscapeAccessSet *aset0,
                     const EscapeAccessSet *aset1);
  static EscapeAccessSet* Copy(const EscapeAccessSet *aset);
  static void Write(Buffer *buf, const EscapeAccessSet *aset);
  static EscapeAccessSet* Read(Buffer *buf);

  static void WriteList(Buffer *buf,
                        const Vector<EscapeAccessSet*> &aset_list);
  static void ReadList(Buffer *buf,
                       Vector<EscapeAccessSet*> *aset_list);

  static void WriteMerge(Buffer *buf, Trace *value,
                         const Vector<EscapeAccess> &accesses);
  static void ReadMerge(Buffer *buf, Trace **pvalue,
                        Vector<EscapeAccess> *paccesses);

  static EscapeAccessSet* Make(Trace *value) {
    EscapeAccessSet xaset(value);
    return g_table.Lookup(xaset);
  }

 public:
  // get the trace location this stores the accesses on.
  Trace* GetValue() const { return m_value; }

  // get the accesses on the value of this set.
  size_t GetAccessCount() const;
  const EscapeAccess& GetAccess(size_t ind) const;

  // add an access to the value in this set of the specified kind
  // at the specified point.
  void AddAccess(const EscapeAccess &access);

  // set the version for the location of a particular access.
  void SetAccessVersion(size_t ind, VersionId version);

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  Trace *m_value;

  // all known accesses on the value.
  Vector<EscapeAccess> *m_accesses;

  EscapeAccessSet(Trace *value);
  static HashCons<EscapeAccessSet> g_table;
};

// escape edge and access generation.

// these functions modify the sets of edges and accesses stored in the
// merge escape caches from storage.h; flushing these caches will write
// out the modified data.

// look for in-memory CSUs when processing CFGs rather than going to the
// CSU cache. used when generating escape edges within the frontend.
void EscapeUseLocalCSUs();

// add to the append escape caches all edges and accesses from the assignments
// and control/data flow in cfg.
void EscapeProcessCFG(BlockCFG *cfg);

// add to the append escape caches all edges resulting from the specified
// call edge invoking the specified callee (directly or indirectly).
void EscapeProcessCall(BlockCFG *cfg, PEdgeCall *edge, Variable *callee);

// escape propagation.

// edge on the escape propagation stack.
struct EscapeStackEdge
{
  // trace reached during escape propagation.
  Trace *source;

  // forward or backward escape edge from source.
  EscapeEdge edge;

  EscapeStackEdge() : source(NULL) {}
  EscapeStackEdge(Trace *_source, const EscapeEdge &_edge)
    : source(_source), edge(_edge)
  {}

  void Print(OutStream &out)
  {
    if (source) {
      out << "  " << source << " -> ";
      edge.Print(out);
      out << endl;
    }
    else {
      out << "  <empty>" << endl;
    }
  }
};

// status structure for performing escape propagation. this should be
// inherited by the various escape algorithms.
class EscapeStatus
{
 public:
  // make empty escape information with the specified exploration direction
  // and cutoff. use cutoff == 0 for no cutoff.
  EscapeStatus(bool forward, size_t cutoff);

  // visit all traces reachable from source via escape edges in a depth first
  // search. the result indicates whether the search was exhaustive;
  // the search is non-exhaustive if the cutoff is reached in terms of numbers
  // of different traces returned by Visit.
  bool FollowEscape(Trace *source);

  // if called within FollowEscape (e.g. by Visit), prints the exploration
  // path up to the current point.
  void PrintEscapeStack();

  // visit a trace location encountered during this escape propagation.
  // if the return value is non-NULL then that is a possibly reduced form
  // of the argument for which further escape propagation should be done.
  // gets a reference on the result. if skip_cutoff is set to true
  // (default is false), the result is not counted towards the escape cutoff.
  virtual Trace* Visit(Trace *trace, bool *skip_cutoff) = 0;

 private:
  // whether this is forward or backward propagation.
  bool m_forward;

  // remaining new locations we can add to visited before hitting the cutoff.
  size_t m_cutoff;

  // whether the cutoff has been reached by some FollowEscape.
  bool m_cutoff_reached;

  // active exploration statck.
  Vector<EscapeStackEdge> m_stack;

  // keys are traces we have visited during this propagation, entries are the
  // top of the exploration stack when the key was first encountered.
  HashTable<Trace*,EscapeStackEdge,HashObject> m_visited;

  // recursive exploration function for FollowEscape.
  void RecursiveEscape(Trace *trace, const EscapeStackEdge &prev);
};

NAMESPACE_XGILL_END
