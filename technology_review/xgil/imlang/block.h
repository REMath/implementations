
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

// control flow graph representation;
// blocks, edges, and points

#include <util/hashcons.h>
#include "bit.h"

NAMESPACE_XGILL_BEGIN

#define ITERATE_BLOCK_KINDS(ITER)					\
  /* entire function body, may contain loops. */			\
  ITER(FunctionWhole, 0)						\
  /* loop-free outer function body, with loop summary edges. */		\
  ITER(Function, 1)							\
  /* loop-free inner loop body, modelling a single iteration. */	\
  ITER(Loop, 2)								\
  /* static initializer of a global variable. */			\
  ITER(Initializer, 3)							\
  /* block computing the value of an annotation. */			\
  ITER(AnnotationFunc, 4)						\
  ITER(AnnotationInit, 5)						\
  ITER(AnnotationComp, 6)

// different kinds of CFG blocks.
enum BlockKind {
#define ITER(NAME, NUM) B_ ## NAME = NUM,
  ITERATE_BLOCK_KINDS(ITER)
#undef ITER
};

// unique identifier for a block
class BlockId : public HashObject
{
 public:
  static int Compare(const BlockId *b0, const BlockId *b1);
  static BlockId* Copy(const BlockId *b);
  static void Write(Buffer *buf, const BlockId *b);
  static BlockId* Read(Buffer *buf, bool clone = false);

  static BlockId* Make(BlockKind kind, Variable *var,
                       String *loop = NULL, bool clone = false) {
    BlockId xb(kind, var, loop, clone);
    return g_table.Lookup(xb);
  }

 public:
  // get the kind of identifier.
  BlockKind Kind() const { return m_kind; }

  // whether this is an identifier for an annotation CFG.
  bool IsAnnotation() const {
    return m_kind == B_AnnotationFunc ||
           m_kind == B_AnnotationInit ||
           m_kind == B_AnnotationComp;
  }

  // get the var/loop of this block. loop is non-NULL only
  // for NULL for B_Loop blocks.
  Variable* BaseVar() const { return m_var; }
  String* Loop() const { return m_loop; }

  // return whether this is a cloned identifier. this flag is not serialized,
  // but when reading a clone can be created instead of the regulard id.
  // clones allow two IDs to exist for the same base identifier.
  bool IsClone() const { return m_clone; }

  // shorthand for getting the name of the base variable, which for functions
  // is the fully decorated name.
  String* Function() const { return m_var->GetName(); }

  // get a more easily human-readable name for a loop, not necessarily unique.
  // this prints to a static buffer so its result is invalidated
  // by a subsequent call to some LoopName.
  const char* LoopName() const;

  // query/set whether this has a write name specified. write names are used
  // to set the real name of a loop ID after it has been initially constructed
  // (loops can't get their full name until after loop splitting has finished).
  // this write name is used instead of the loop name when serializing.
  String* WriteLoop() const { return m_write_loop; }
  void SetWriteLoop(String *name);

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;

 private:
  BlockKind m_kind;
  Variable *m_var;
  String *m_loop;
  bool m_clone;

  // alternate write name for loop IDs.
  String *m_write_loop;

  BlockId(BlockKind kind, Variable *var, String *loop, bool clone);

 public:
  static HashCons<BlockId> g_table;
};

// version identifier for a block. versions start at zero for the original
// clean build, and increase as incremental builds are performed which change
// the block (changes preserving equivalence do not affect the version).
typedef size_t VersionId;

// a block identifier and program point, identifying a point in the program.
// these may be versioned, indicating the version of the CFG containing
// the point. versioned BlockPPoints are used when storing information that
// may otherwise go out of sync after an incremental analysis.
struct BlockPPoint
{
  static void Write(Buffer *buf, BlockPPoint bp);
  static BlockPPoint Read(Buffer *buf);

  BlockId *id;
  PPoint point;
  VersionId version;

  BlockPPoint() : id(NULL), point(0), version(0) {}
  BlockPPoint(BlockId *_id, PPoint _point, VersionId _version = 0)
    : id(_id), point(_point), version(_version) {}

  bool operator == (const BlockPPoint &o) const {
    return id == o.id && point == o.point && version == o.version;
  }

  bool operator != (const BlockPPoint &o) const {
    return id != o.id || point != o.point || version != o.version;
  }

  static int Compare(const BlockPPoint &v0, const BlockPPoint &v1)
  {
    int cmp = BlockId::Compare(v0.id, v1.id);
    if (cmp) return cmp;

    if (v0.point < v1.point) return -1;
    if (v0.point > v1.point) return 1;
    if (v0.version < v1.version) return -1;
    if (v0.version > v1.version) return 1;
    return 0;
  }

  static bool Similar(const BlockPPoint &v0, const BlockPPoint &v1)
  {
    // equality for two blocks, except for two points in the same static
    // initializer where we want to avoid possible blowup.
    return (v0.id == v1.id) && (v0.version == v1.version) &&
      (v0.id->Kind() == B_Initializer || v0.point == v1.point);
  }
};

// print block/point identifiers directly to a stream.
inline OutStream& operator << (OutStream &out, const BlockPPoint &bp)
{
  out << bp.id;
  if (bp.version) out << "#" << bp.version;
  out << ":" << bp.point;
  return out;
}

// the different kinds of annotations.
enum AnnotationKind {
  AK_Invalid = 0,

#define XIL_FILL_ANNOT(NAME, _, VALUE)  AK_ ## NAME = VALUE,
  XIL_ITERATE_ANNOT(XIL_FILL_ANNOT)
#undef XIL_FILL_ANNOT

};

// get the string representation of an annotation kind.
inline const char* AnnotationKindString(AnnotationKind kind)
{
  switch (kind) {

#define XIL_PRINT_ANNOT(NAME, STR, _)  case AK_ ## NAME: return STR; break;
  XIL_ITERATE_ANNOT(XIL_PRINT_ANNOT)
#undef XIL_PRINT_ANNOT

  default: Assert(false);
  }
}

class PEdge;

// information about a variable defined by a CFG.
struct DefineVariable
{
  // variable being defined.
  Variable *var;

  // type of the variable.
  Type *type;

  DefineVariable() : var(NULL), type(NULL) {}
  DefineVariable(Variable *_var, Type *_type) : var(_var), type(_type) {}
};

// information about a potential loop head in a CFG.
struct LoopHead
{
  // point in the CFG where back edges might target.
  PPoint point;

  // source location to use for the exit point of the loop CFG,
  // if this is found to be a loop. may be NULL.
  Location *end_location;

  LoopHead() : point(0), end_location(NULL) {}
  LoopHead(PPoint _point, Location *_end_location)
    : point(_point), end_location(_end_location) {}
};

// information about a point annotation in a CFG. in contrast to annotations
// on edges, which came from assertions in the source code, these come from
// the web interface and can be inserted without changing the CFG's structure.
struct PointAnnotation
{
  // point where this annotation occurs at.
  PPoint point;

  // ID of the annotation CFG.
  BlockId *annot;

  PointAnnotation() : point(0), annot(NULL) {}
  PointAnnotation(PPoint _point, BlockId *_annot)
    : point(_point), annot(_annot) {}
};

// a control flow graph - points and edges with distinguished entry/exit
// points. depending on the ID for the CFG this graph may or may not
// contain loops.
class BlockCFG : public HashObject
{
 public:
  static int Compare(const BlockCFG *cfg0, const BlockCFG *cfg1);
  static BlockCFG* Copy(const BlockCFG *cfg);
  static void Write(Buffer *buf, const BlockCFG *cfg);
  static BlockCFG* Read(Buffer *buf, bool clone = false);

  // read/write methods for lists of CFGs.
  static void WriteList(Buffer *buf, const Vector<BlockCFG*> &cfgs);
  static void ReadList(Buffer *buf, Vector<BlockCFG*> *cfgs,
                       bool clone = false);

  static BlockCFG* Make(BlockId *id)
  {
    BlockCFG xcfg(id);
    return g_table.Lookup(xcfg);
  }

 public:
  // get the unique identifier for this block.
  BlockId* GetId() const { return m_id; }

  // get the version of this block.
  size_t GetVersion() const { return m_version; }

  // get the command used to construct this block.
  String* GetCommand() const { return m_command; }

  // get the begin and end source locations of this block.
  Location* GetBeginLocation() const {
    Assert(m_begin_location);
    return m_begin_location;
  }
  Location* GetEndLocation() const {
    Assert(m_end_location);
    return m_end_location;
  }

  // get all the non-global variables defined for this block.
  const Vector<DefineVariable>* GetVariables() const { return m_vars; }

  // get the type associated with a variable defined by this block,
  // NULL if the variable is not defined by this block.
  Type* GetVariableType(const Variable *var) const {
    if (m_vars) {
      for (size_t vind = 0; vind < m_vars->Size(); vind++) {
        if (var == m_vars->At(vind).var)
          return m_vars->At(vind).type;
      }
    }
    return NULL;
  }

  // finds a variable in the list of variables defined by this block
  // which matches the specified var, returning that var if found,
  // NULL otherwise.
  Variable* FindMatchingVariable(Variable *var) const;

  // get the parent of this loop, if it exists. only used for B_Loop.
  size_t GetLoopParentCount() const {
    return m_loop_parents ? m_loop_parents->Size() : 0;
  }
  BlockPPoint GetLoopParent(size_t ind) const {
    Assert(m_loop_parents);
    return m_loop_parents->At(ind);
  }

  // get the points in this block. valid PPoint values for this block
  // are the range [1,GetPointCount()]
  size_t GetPointCount() const {
    return m_points ? m_points->Size() : 0;
  }

  // get the source location of a particular point.
  Location* GetPointLocation(PPoint point) const {
    Assert(m_points);
    Assert(point);
    return m_points->At(point - 1);
  }

  // get the entry/exit points in this block.
  PPoint GetEntryPoint() const { return m_entry_point; }
  PPoint GetExitPoint() const { return m_exit_point; }

  // get the potential loop heads in this block. not used for B_Function
  // or B_Loop, these are just candidates for use during loop splitting.
  size_t GetLoopHeadCount() const {
    return m_loop_heads ? m_loop_heads->Size() : 0;
  }
  const LoopHead& GetLoopHead(size_t ind) const {
    Assert(m_loop_heads);
    return m_loop_heads->At(ind);
  }

  // returns whether point is isomorphic to a point in the CFG for an
  // inner loop. code in a syntactic loop body will be reflected in CFGs
  // for both the loop and its parent (and transitive parents) if it may
  // reach both the recursive loop edge and a loop exit point. this common
  // code will be isomorphic between the two CFGs. this is computed during
  // loop splitting and only applies to B_Function and B_Loop cfgs.
  bool IsLoopIsomorphic(PPoint point) const {
    return m_loop_isomorphic ? m_loop_isomorphic->Contains(point) : false;
  }

  // get the edges in this block.
  size_t GetEdgeCount() const {
    return m_edges ? m_edges->Size() : 0;
  }
  PEdge* GetEdge(size_t ind) const {
    Assert(m_edges);
    return m_edges->At(ind);
  }

  // get the point annotations in this block.
  size_t GetPointAnnotationCount() const {
    return m_point_annotations ? m_point_annotations->Size() : 0;
  }
  const PointAnnotation& GetPointAnnotation(size_t ind) const {
    Assert(m_point_annotations);
    return m_point_annotations->At(ind);
  }

  // return whether this CFG is equivalent to cfg. these CFGs should be for
  // the same function or loop, and either this or cfg will have a clone ID.
  // two CFGs are equivalent if they are identical except for location info.
  bool IsEquivalent(BlockCFG *cfg) const;

  // annotation CFG methods.

  // if this is an annotation CFG, get/set the kind of annotation.
  AnnotationKind GetAnnotationKind() const { return m_annotation_kind; }
  void SetAnnotationKind(AnnotationKind kind);

  // get/set the actual computed bit for this annotation. SetBit can be NULL
  // if the annotation is broken and there was an error while processing it.
  Bit* GetAnnotationBit() const { return m_annotation_bit; }
  void SetAnnotationBit(Bit *bit);

  // whether the bit has been computed for this annotation CFG.
  bool IsAnnotationBitComputed() const { return m_annotation_computed; }

  // modification methods.

  // set the version of this block, and all loop parents of this block.
  void SetVersion(VersionId version);

  // set the command for generating this block.
  void SetCommand(String *command);

  // set the begin and end locations of this function in the source.
  void SetBeginLocation(Location *loc);
  void SetEndLocation(Location *loc);

  // add a variable to the list of non-global variables accessible in this CFG.
  void AddVariable(Variable *var, Type *type);

  // add a loop parent of this CFG.
  void AddLoopParent(BlockPPoint where);

  // clears out the points, edges, and loop heads from this CFG.
  void ClearBody();

  // clears just the loop heads from this CFG.
  void ClearLoopHeads();

  // add a new point to this CFG with the specified source location.
  // consumes a reference on loc.
  PPoint AddPoint(Location *loc);

  // change the location of an existing point in this CFG.
  // consumes a reference on loc.
  void SetPointLocation(PPoint point, Location *loc);

  // set the entry/exit point of this CFG.
  void SetEntryPoint(PPoint point);
  void SetExitPoint(PPoint point);

  // add a loop head to this CFG.
  void AddLoopHead(PPoint point, Location *end_location);

  // adds an isomorphic point to this CFG.
  void AddLoopIsomorphic(PPoint point);

  // add a new edge to this CFG between the specified points.
  // consumes a reference on edge.
  void AddEdge(PEdge *edge);

  // replace an existing edge at the specified index with a new edge.
  // consumes a reference on edge.
  void SetEdge(size_t eind, PEdge *edge);

  // add a point annotation to this CFG.
  void AddPointAnnotation(PPoint point, BlockId *annot);

  // helper methods.

  // get a list of the outgoing/incoming edges for a point. if these are
  // called the CFG cannot be modified with new edges later.
  const Vector<PEdge*>& GetOutgoingEdges(PPoint point);
  const Vector<PEdge*>& GetIncomingEdges(PPoint point);

  // get the single outgoing edge there is for point. if the point has
  // zero or multiple outgoing edges, fail or return NULL per required.
  PEdge* GetSingleOutgoingEdge(PPoint point, bool required = true);

  // point is the origin of a PEdgeCall rather than a PEdgeLoop.
  // fail when called on non-call/loop points.
  bool PointEdgeIsCall(PPoint point);

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  BlockId *m_id;

  VersionId m_version;
  String *m_command;

  Location *m_begin_location;
  Location *m_end_location;

  // variables in scope for this CFG. also includes the global/function
  // being declared.
  Vector<DefineVariable> *m_vars;

  // if this is B_Loop, indicates the point(s) in the parent loop or outer
  // function body where this loop is invoked. a loop may have multiple
  // parents if its entry point appears in the body both for another loop
  // and for the parent of that loop. these are versioned.
  Vector<BlockPPoint> *m_loop_parents;

  // potential loop heads in this CFG. only used before loop splitting.
  Vector<LoopHead> *m_loop_heads;

  // points in this CFG which are isomorphic to a point in a loop CFG.
  // only available after loop splitting.
  Vector<PPoint> *m_loop_isomorphic;

  // locations of each point. m_points[n] is the location of point (n+1).
  Vector<Location*> *m_points;

  // block entry/exit points.
  PPoint m_entry_point;
  PPoint m_exit_point;

  // the edges in this CFG.
  Vector<PEdge*> *m_edges;

  // the point annotations in this CFG.
  Vector<PointAnnotation> *m_point_annotations;

  // if this is an annotation CFG, the annotation kind and bit (if computed).
  AnnotationKind m_annotation_kind;
  bool m_annotation_computed;
  Bit *m_annotation_bit;

  typedef HashTable< PPoint, PEdge*, DataHash<PPoint> > EdgeTable;

  // tables of the outgoing and incoming edges for each point.
  EdgeTable *m_outgoing_edges;
  EdgeTable *m_incoming_edges;

  // compute the outgoing/incoming edges and fill in m_computed_edges,
  // if we have not already done so.
  void ComputeEdgeInfo();
  void ClearEdgeInfo();

  // empty CFG which we will fill in later on.
  BlockCFG(BlockId *id);

 public:
  static HashCons<BlockCFG> g_table;
};

// HashCons tables

#define ITERATE_EDGE_KINDS(ITER)		\
  ITER(Skip, 1)					\
  ITER(Assume, 2)				\
  ITER(Assign, 3)				\
  ITER(Call, 4)					\
  ITER(Loop, 5)					\
  ITER(Assembly, 6)				\
  ITER(Annotation, 7)

enum PEdgeKind {
  EGK_Invalid = 0,
#define ITER(NAME, NUM) EGK_ ## NAME = NUM,
  ITERATE_EDGE_KINDS(ITER)
#undef ITER
};

class PEdgeSkip;
class PEdgeAssume;
class PEdgeAssign;
class PEdgeCall;
class PEdgeLoop;
class PEdgeAssembly;
class PEdgeAnnotation;

class PEdge : public HashObject
{
 public:
  static int Compare(const PEdge *e0, const PEdge *e1);
  static PEdge* Copy(const PEdge *e);
  static void Write(Buffer *buf, const PEdge *e);
  static PEdge* Read(Buffer *buf);

  static PEdge* MakeSkip(PPoint source, PPoint target);
  static PEdge* MakeAssume(PPoint source, PPoint target,
                           Exp *cond, bool nonzero);
  static PEdge* MakeAssign(PPoint source, PPoint target, Type *type,
                           Exp *left_side, Exp *right_side);
  static PEdge* MakeCall(PPoint source, PPoint target, TypeFunction *type,
                         Exp *return_value, Exp *instance, Exp *function,
                         const Vector<Exp*> &arguments);
  static PEdge* MakeLoop(PPoint source, PPoint target, BlockId *loop);
  static PEdge* MakeAssembly(PPoint source, PPoint target);
  static PEdge* MakeAnnotation(PPoint source, PPoint target, BlockId *annot);

  // get a reference on an edge equivalent to e except with a
  // new source and target.
  static PEdge* ChangeEdge(const PEdge *e, PPoint source, PPoint target);

  // compare two edges, ignoring the source and target points.
  static int CompareInner(const PEdge *e0, const PEdge *e1);

 public:
  // get the kind of edge
  PEdgeKind Kind() const { return m_kind; }

  // get the source/target of the edge. the target may be 0
  PPoint GetSource() const { return m_source; }
  PPoint GetTarget() const { return m_target; }

  DOWNCAST_TYPE(PEdge, EGK_, Skip)
  DOWNCAST_TYPE(PEdge, EGK_, Assume)
  DOWNCAST_TYPE(PEdge, EGK_, Assign)
  DOWNCAST_TYPE(PEdge, EGK_, Call)
  DOWNCAST_TYPE(PEdge, EGK_, Loop)
  DOWNCAST_TYPE(PEdge, EGK_, Assembly)
  DOWNCAST_TYPE(PEdge, EGK_, Annotation)

  // print this edge for the UI.
  virtual void PrintUI(OutStream &out) const = 0;

  // invoke the visitor on all or a portion of the expressions used to execute
  // this edge, according to the kind of visitor. if there are assignments of
  // structure-typed values on this edge then the visitor will be invoked for
  // each transitive field. in this case the expressions visited may no longer
  // exist after the VisitLvals() finishes, so if the visitor wants to ensure
  // the expressions persist until after the visit, that visitor needs to add
  // extra references on those expressions.
  virtual void DoVisit(ExpVisitor *visitor) const {}

  // if this edge is a direct call or loop invocation of another
  // block, get a reference on the ID of that block.
  virtual BlockId* GetDirectCallee() const { return NULL; }

 protected:
  PEdgeKind m_kind;
  PPoint m_source;
  PPoint m_target;

  PEdge(PEdgeKind kind, PPoint source, PPoint target)
    : m_kind(kind), m_source(source), m_target(target)
  {
    // m_target allowed to be 0
    Assert(m_source > 0);

    m_hash = Hash32(m_kind, m_source);
    m_hash = Hash32(m_hash, m_target);
  }

 public:
  static HashCons<PEdge> g_table;
};

// PEdge instance classes

class PEdgeSkip : public PEdge
{
 public:
  // inherited methods
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;

 private:
  PEdgeSkip(PPoint source, PPoint target);
  friend class PEdge;
};

class PEdgeAssume : public PEdge
{
 public:
  // get the condition assumed to be nonzero or iszero along this edge.
  Exp* GetCondition() const { return m_cond; }

  // whether this should is assuming the expression is nonzero vs. iszero.
  bool IsNonZero() const { return m_nonzero; }

  // inherited methods
  void DoVisit(ExpVisitor *visitor) const;
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;
  void MarkChildren() const;

 private:
  Exp *m_cond;
  bool m_nonzero;

  PEdgeAssume(PPoint source, PPoint target, Exp *cond, bool nonzero);
  friend class PEdge;
};

class PEdgeAssign : public PEdge
{
 public:
  // get the type of the value being assigned
  Type* GetType() const { return m_type; }

  // get the left side of this assignment
  Exp* GetLeftSide() const { return m_left_side; }

  // get the right side of this assignment
  Exp* GetRightSide() const { return m_right_side; }

  // inherited methods
  void DoVisit(ExpVisitor *visitor) const;
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;
  void MarkChildren() const;

 private:
  Type *m_type;
  Exp *m_left_side;
  Exp *m_right_side;

  PEdgeAssign(PPoint source, PPoint target, Type *type,
              Exp *left_side, Exp *right_side);
  friend class PEdge;
};

class PEdgeCall : public PEdge
{
 public:
  // get the type of the function being invoked. this will contain
  // the types of the return value and call arguments.
  TypeFunction* GetType() const { return m_type; }

  // get the location where the return value of this call is stored,
  // NULL if it has no return value or its return value is not stored.
  Exp* GetReturnValue() const { return m_return_value; }

  // get the instance object for this call. this is only non-NULL for instance calls
  // on C++ structs or classes.
  Exp* GetInstanceObject() const { return m_instance_object; }

  // get the expression for the function which was invoked. for instance calls
  // this is either a specific function (non-virtual functions), or an offset
  // from the instance object.
  Exp* GetFunction() const { return m_function; }

  // get the number of actual arguments.
  size_t GetArgumentCount() const { return m_argument_count; }

  // get an argument at a particular index.
  Exp* GetArgument(size_t ind) const
  {
    Assert(ind < m_argument_count);
    return m_arguments[ind];
  }

  // get the name of the function this is a direct call to, if it is
  // a direct call. this includes non-virtual instance calls. NULL otherwise.
  Variable* GetDirectFunction() const;

  // inherited methods
  BlockId* GetDirectCallee() const;
  void DoVisit(ExpVisitor *visitor) const;
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  TypeFunction *m_type;
  Exp *m_return_value;
  Exp *m_instance_object;
  Exp *m_function;

  Exp **m_arguments;
  size_t m_argument_count;

  PEdgeCall(PPoint source, PPoint target, TypeFunction *type,
            Exp *return_value, Exp *instance, Exp *function,
            const Vector<Exp*> &arguments);

  friend class PEdge;
};

class PEdgeLoop : public PEdge
{
 public:
  // get the identifier of the loop being invoked
  BlockId* GetLoopId() const { return m_loop; }

  // inherited methods
  BlockId* GetDirectCallee() const;
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;
  void MarkChildren() const;

 private:
  BlockId *m_loop;

  PEdgeLoop(PPoint source, PPoint target, BlockId *loop);
  friend class PEdge;
};

class PEdgeAssembly : public PEdge
{
 public:
  // inherited methods
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;

 private:
  PEdgeAssembly(PPoint source, PPoint target);
  friend class PEdge;
};

// annotation edges have no side effects, they merely indicate the placement
// of an assert/assume annotation from the source.
class PEdgeAnnotation : public PEdge
{
 public:
  // get the identifier of the annotation at this point.
  BlockId* GetAnnotationId() const { return m_annot; }

  // inherited methods
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;
  void MarkChildren() const;

 private:
  BlockId *m_annot;

  PEdgeAnnotation(PPoint source, PPoint target, BlockId *annot);
  friend class PEdge;
};

// various hashing structures.

struct PPointPair
{
  PPoint first;
  PPoint second;

  PPointPair() : first(0), second(0) {}
  PPointPair(PPoint _first, PPoint _second) : first(_first), second(_second) {}

  bool operator ==(const PPointPair &p) const {
    return first == p.first && second == p.second;
  }

  static uint32_t Hash(uint32_t hash, const PPointPair &v) {
    hash = Hash32(hash, v.first);
    return Hash32(hash, v.second);
  }
};

typedef DataHash<PPoint> hash_PPoint;

typedef HashSet<PPoint,hash_PPoint> PPointHash;
typedef HashSet<PPointPair,PPointPair> PPointPairHash;
typedef HashTable<PPoint,PPoint,hash_PPoint> PPointListHash;
typedef HashSet<PEdge*,HashObject> PEdgeHash;

NAMESPACE_XGILL_END
