
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

// local memory model definitions

#include <imlang/block.h>
#include <imlang/trace.h>
#include "alias.h"
#include "clobber.h"
#include "simplify.h"

NAMESPACE_XGILL_BEGIN

// ways in which an exp/bit can be translated.
enum TranslateKind {
  // convert value relative to point.
  TRK_Point,

  // convert value absolute in loop/call callee.
  TRK_Callee,

  // as with TRK_Callee, with all ExpDrf treated as ExpExit.
  TRK_CalleeExit,

  // convert ExpExit to actual values of the lval at exit.
  // point must be the exit point of the block.
  TRK_Exit,

  // remove ExpClobber side effects at point, as if the value was not
  // clobbered at all (can only be used at loop edges, as loops may execute
  // zero times).
  TRK_SkipClobber,

  // remove all ExpVal from the value. this is transitive, so that
  // the result will not have any Val expressions in it.
  TRK_RemoveVal,

  // as in RemoveVal, except cuts off if a blowup in the number of results
  // is detected, so there may still be remaining ExpVal.
  TRK_TryRemoveVal
};

struct PointExp
{
  Exp *exp;
  PPoint point;

  PointExp() : exp(NULL), point(0)
  {}

  PointExp(Exp *_exp, PPoint _point) : exp(_exp), point(_point)
  {}

  bool operator == (const PointExp &o) const {
    return exp == o.exp && point == o.point;
  }

  static uint32_t Hash(uint32_t hash, const PointExp &v) {
    hash = Hash32(hash, v.exp->Hash());
    return Hash32(hash, v.point);
  }
};

struct PointBit
{
  Bit *bit;
  PPoint point;

  PointBit() : bit(NULL), point(0)
  {}

  PointBit(Bit *_bit, PPoint _point) : bit(_bit), point(_point)
  {}

  bool operator == (const PointBit &o) const {
    return bit == o.bit && point == o.point;
  }

  static uint32_t Hash(uint32_t hash, const PointBit &v) {
    hash = Hash32(hash, v.bit->Hash());
    return Hash32(hash, v.point);
  }
};

struct PointValue
{
  Exp *lval;
  Exp *kind;
  PPoint point;

  PointValue() : lval(NULL), kind(NULL), point(0)
  {}

  PointValue(Exp *_lval, Exp *_kind, PPoint _point)
    : lval(_lval), kind(_kind), point(_point)
  {}

  bool operator == (const PointValue &o) const {
    return lval == o.lval && kind == o.kind && point == o.point;
  }

  static uint32_t Hash(uint32_t hash, const PointValue &v) {
    hash = Hash32(hash, v.lval->Hash());
    if (v.kind)
      hash = Hash32(hash, v.kind->Hash());
    return Hash32(hash, v.point);
  }
};

struct PointTranslate
{
  TranslateKind kind;
  PPoint point;
  Exp *exp;

  PointTranslate() : kind(TRK_Point), point(0), exp(NULL)
  {}

  PointTranslate(TranslateKind _kind, PPoint _point, Exp *_exp)
    : kind(_kind), point(_point), exp(_exp)
  {}

  bool operator == (const PointTranslate &o) const {
    return kind == o.kind && point == o.point && exp == o.exp;
  }

  static uint32_t Hash(uint32_t hash, const PointTranslate &v) {
    hash = Hash32(hash, v.kind);
    hash = Hash32(hash, v.point);
    return Hash32(hash, v.exp->Hash());
  }
};

struct GuardTrueFalse
{
  Bit *true_guard;
  Bit *false_guard;

  GuardTrueFalse()
    : true_guard(NULL), false_guard(NULL)
  {}

  GuardTrueFalse(Bit *_true_guard, Bit *_false_guard)
    : true_guard(_true_guard), false_guard(_false_guard)
  {
    Assert(true_guard);
    Assert(false_guard);
  }
};

// guarded assignment of an rvalue to an lvalue.
struct GuardAssign
{
  Exp *left;
  Exp *right;
  Bit *guard;

  // kind of assignment, per BlockMemory::GetVal.
  Exp *kind;

  GuardAssign()
    : left(NULL), right(NULL), guard(NULL), kind(NULL)
  {}

  GuardAssign(Exp *_left, Exp *_right, Bit *_guard, Exp *_kind = NULL)
    : left(_left), right(_right), guard(_guard), kind(_kind)
  {
    Assert(left);
    Assert(right);
    Assert(guard);
  }

  bool operator == (const GuardAssign &o) const {
    return left == o.left && right == o.right &&
           guard == o.guard && kind == o.kind;
  }
};

struct GuardExp
{
  Exp *exp;
  Bit *guard;

  GuardExp()
    : exp(NULL), guard(NULL)
  {}

  GuardExp(Exp *_exp, Bit *_guard)
    : exp(_exp), guard(_guard)
  {
    Assert(exp);
    Assert(guard);
  }

  HashObject* ValueData() { return exp; }
};

struct GuardBit
{
  Bit *bit;
  Bit *guard;

  GuardBit()
    : bit(NULL), guard(NULL)
  {}

  GuardBit(Bit *_bit, Bit *_guard)
    : bit(_bit), guard(_guard)
  {
    Assert(bit);
    Assert(guard);
  }

  HashObject* ValueData() { return bit; }
};

// vector of guarded objects which manages its own references.
template <class T, class V>
class GuardVector
{
 public:
  GuardVector<T,V>() {}
  ~GuardVector<T,V>() { Clear(); }

  // copy disallowed.
  GuardVector<T,V>& operator = (const GuardVector<T,V>&) { Assert(false); }
  GuardVector<T,V>(const GuardVector<T,V>&) { Assert(false); }

  const T& At(size_t n) const { return m_vector[n]; }
  const T& operator [](size_t n) const { return m_vector[n]; }

  bool Empty() const { return m_vector.Empty(); }
  size_t Size() const { return m_vector.Size(); }

  void PushBack(const T &v)
  {
    if (!v.guard->IsFalse())
      m_vector.PushBack(v);
  }

  void Clear()
  {
    m_vector.Clear();
  }

  // add all entries from vector to this guarded vector.
  void FillFromVector(const Vector<T> &ovec)
  {
    for (size_t ind = 0; ind < ovec.Size(); ind++)
      PushBack(ovec[ind]);
  }

  // add all entries from this guarded vector to the specified vector.
  void FillVector(Vector<T> *ovec)
  {
    for (size_t ind = 0; ind < Size(); ind++)
      ovec->PushBack(m_vector[ind]);
  }

  // sort and combine duplicates in this guarded vector. if two entries
  // differ only in their guard then make a single entry with a disjunction
  // for the guard.
  void SortCombine()
  {
    if (Size() <= 1)
      return;

    bool changed;
    do {
      changed = false;
      for (size_t ind = 0; ind < Size() - 1; ind++) {
        T &t0 = m_vector[ind];
        T &t1 = m_vector[ind + 1];

        V *v0 = (V*) t0.ValueData();
        V *v1 = (V*) t1.ValueData();

        int res = CompareObjects<V>(v0, v1);
        if (res == 0) {
          t0.guard = Bit::MakeOr(t0.guard, t1.guard);

          t1 = m_vector.Back();
          m_vector.PopBack();

          changed = true;
        }
        else if (res > 0) {
          T tmp = t0;
          t0 = t1;
          t1 = tmp;

          changed = true;
        }
      }
    } while (changed);
  }

  // simplify the guards on elements in this vector if possible.
  void SimplifyGuards()
  {
    // one-value case: drive the answer to true.
    if (Size() == 1) {
      T &v = m_vector[0];
      if (!v.guard->IsTrue())
        v.guard = Bit::MakeConstant(true);
    }

    // two-value case: if one bit is more complex than the other, make it the
    // negation of the simpler bit.
    if (Size() == 2) {
      T &v0 = m_vector[0];
      T &v1 = m_vector[1];
      size_t size0 = v0.guard->Size();
      size_t size1 = v1.guard->Size();

      if (size0 + 1 < size1)
        v1.guard = Bit::MakeNot(v0.guard);
      else if (size1 + 1 < size0)
        v0.guard = Bit::MakeNot(v1.guard);
    }
  }

  // internal data representation.
  Vector<T> m_vector;
};

typedef GuardVector<GuardExp,Exp> GuardExpVector;
typedef GuardVector<GuardBit,Bit> GuardBitVector;

// BlockMemory representation of the behavior of a BlockCFG.

class BlockMemory : public HashObject
{
 public:
  static int Compare(const BlockMemory *mcfg0, const BlockMemory *mcfg1);
  static BlockMemory* Copy(const BlockMemory *mcfg);
  static void Write(Buffer *buf, const BlockMemory *mcfg);
  static BlockMemory* Read(Buffer *buf);

  static void WriteList(Buffer *buf, const Vector<BlockMemory*> &mcfg_list);
  static void ReadList(Buffer *buf, Vector<BlockMemory*> *mcfg_list);

  static BlockMemory* Make(BlockId *id,
                           MemorySimplifyKind simplify_kind,
                           MemoryAliasKind alias_kind,
                           MemoryClobberKind clobber_kind) {
    BlockMemory xmcfg(id, simplify_kind, alias_kind, clobber_kind);
    return g_table.Lookup(xmcfg);
  }

  // gets the bit associated with an annotation, computing it if necessary.
  // bits containing directives will be skipped per skip_directives.
  // msg_out receives any error message for the annotation.
  static Bit* GetAnnotationBit(BlockCFG *annot_cfg, bool skip_directives = true,
                               ostream *msg_out = NULL);

 public:
  // get the ID of the CFG for this block.
  BlockId* GetId() const { return m_id; }

  // set the CFG for this block. cfg->GetId() == GetId().
  // holds a reference on cfg which persists until the BlockMemory goes away.
  void SetCFG(BlockCFG *cfg);

  // get the CFG for this block, if it has been set.
  BlockCFG* GetCFG() const { return m_cfg; }

  // fill in all the persistent tables with information computed from the CFG.
  // requires that the cfg has been set.
  void ComputeTables();

  // get the guard for the specified point, the condition under which
  // that point is executed during a run of the function.
  Bit* GetGuard(PPoint point) const;

  // get the edge condition for the specified edge, the condition under which
  // control transfers along that edge provided it reaches the source.
  // if the condition is just 'true', returns NULL.
  Bit* GetEdgeCond(PEdge *edge) const;

  // get a reference on the edge transfer condition where both the source
  // point of the edge is executed and control transfers along this edge.
  Bit* GetEdgeTransfer(PEdge *edge) const;

  // get a reference on a condition new_guard such that:
  // (GetGuard(edge_source) && guard) <==>
  // (GetGuard(edge_target) && GetEdgeCond(edge) && new_guard)
  // consumes a reference on guard and adds a reference on new_guard.
  Bit* GetEdgeGuard(PEdge *edge, Bit *guard) const;

  // get the state changes and information occurring at each point,
  // NULL if there are none.
  const Vector<GuardExp>* GetReturns(PPoint point) const;
  const Vector<GuardExp>* GetTargets(PPoint point) const;
  const Vector<GuardAssign>* GetAssigns(PPoint point) const;
  const Vector<GuardAssign>* GetArguments(PPoint point) const;

  // get the possible values of lval at the specified point.
  // the result will not be a single ExpVal at point, but may contain ExpVal
  // from earlier points in the block.
  const Vector<GuardExp>& GetVal(Exp *lval, Exp *kind, PPoint point);

  // as in GetVal, except the result may be simplified to a single ExpVal
  // at point if appropriate.
  void GetValSimplify(Exp *lval, Exp *kind, PPoint point,
                      GuardExpVector *res);

  // as in GetVal, except the result expressions will not refer at all
  // to ExpVal exps (the associated guards may contain ExpVal, however).
  // if use_try_remove is set then uses TryRemoveVal rather than RemoveVal,
  // so will return Val expressions rather than blowing up.
  void GetValComplete(Exp *lval, Exp *kind, PPoint point,
                      GuardExpVector *res, bool use_try_remove = false);

  // translate an exp/bit according to the specified TranslateKind and point.
  void TranslateExp(TranslateKind kind, PPoint point, Exp *exp,
                    GuardExpVector *res);
  void TranslateBit(TranslateKind kind, PPoint point, Bit *bit,
                    GuardBitVector *res);

  // alternate form of TranslateBit which combines all the bits in the
  // translation result: (bit0 & guard0) | (bit1 & guard1) | ...
  void TranslateBit(TranslateKind kind, PPoint point, Bit *bit, Bit **res);

  // translate an entire assignment.
  void TranslateAssign(TranslateKind kind, PPoint point, Type *type,
                       Exp *left, Exp *right, Bit *when,
                       Vector<GuardAssign> *res);

  // get the expressions for the function pointer used to invoke an indirect
  // call, either the straight fnptr target or object/field for virtual calls.
  void TranslateReceiver(PPoint point, GuardExpVector *res);

  // return whether exp or bit can be translated at the call/loop site
  // at the specified point. an exp/bit may fail to translate if it refers
  // to invalid data such as missing arguments or return values. the exp/bit
  // must be valid for translation, e.g. it does not refer to local variables
  // for a call or to Clobber/Val/etc. expressions.
  bool CanTranslateCalleeExp(PPoint point, Exp *exp);
  bool CanTranslateCalleeBit(PPoint point, Bit *bit);

  // transfer function for the initial value of lval at entry to the block.
  void TransferEntry(Exp *lval, Exp *kind, GuardExpVector *res);

  // transfer function for the value of lval after transfer along edge.
  // does *not* incorporate the edge transfer conditions in the result guards;
  // to get these, GetEdgeGuard must be used.
  void TransferEdge(Exp *lval, Exp *kind, PEdge *edge, GuardExpVector *res);

  // other utility methods.

  // is lval clobbered by the specified edge? if so the callee lval through
  // which the clobber occurs is returned through inner, as well as the guard
  // where the clobber occurs.
  bool IsLvalClobbered(Exp *lval, Exp *kind, PEdge *edge,
                       Exp **inner, Bit **guard);

  // get whether the value of exp/bit changes from entry to exit of this block.
  bool IsExpPreserved(Exp *exp);
  bool IsBitPreserved(Bit *bit);

  // get the condition where writing to update can change lval.
  // handle the builtin case where identical lvalues always alias.
  Bit* IsLvalAliased(Exp *update, Exp *lval, Exp *kind)
  {
    if (update == lval)
      return Bit::MakeConstant(true);
    return m_alias->CheckAlias(this, update, lval, kind);
  }

  // if lval should be considered as an index of the specified stride type
  // into some buffer, gets a reference to the base of that buffer.
  // otherwise returns lval.
  Exp* GetBaseBuffer(Exp *lval, Type *stride_type);

  // if left is assigned right at point and this assignment establishes
  // a terminator, gets a reference on that terminator kind and returns the
  // terminator lvalue through *lval.
  ExpTerminate* GetTerminateAssign(PPoint point, Exp *left, Exp *right,
                                   Exp **lval);

  // whether an edge may induce a GC.
  bool EdgeCanGC(PEdge *edge);

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:

  // ID of the cfg this is generating memory information for.
  BlockId *m_id;

  // cfg this is generating memory information for.
  BlockCFG *m_cfg;

  // backends for queries used to generate memory information.
  MemorySimplify *m_simplify;
  MemoryAlias *m_alias;
  MemoryClobber *m_clobber;

  // have we computed the persistent tables?
  // this can be done directly or by reading in their contents from a stream
  bool m_computed;

  // persistent tables. these are computed eagerly and are remembered when
  // the BlockMemory is read/written. all other info is directly derived
  // from these tables.

  // table of the guard at each point.
  typedef HashTable<PPoint,Bit*,hash_PPoint> GuardTable;
  GuardTable *m_guard_table;

  // table of transfer conditions along each assume edge.
  // the true_guard/false_guard in the GuardTrueFalse indicate the condition
  // for the outgoing IsNonZero() and IsZero() edges of the source point.
  typedef HashTable<PPoint,GuardTrueFalse,hash_PPoint> AssumeTable;
  AssumeTable *m_assume_table;

  typedef HashTable<PPoint,GuardExp,hash_PPoint> GuardExpTable;

  // table of the callsite return lvalues at each call point.
  GuardExpTable *m_return_table;

  // table of the function or instance object lvalues at each call point.
  GuardExpTable *m_target_table;

  typedef HashTable<PPoint,GuardAssign,hash_PPoint> GuardAssignTable;

  // table of the assignments performed at each point.
  GuardAssignTable *m_assign_table;

  // table of all the values directly passed as arguments at each call point.
  GuardAssignTable *m_argument_table;

  // table of clobbered lvalues, indicating the new value of an lvalue after
  // being overwritten by a call/loop at some point. these lists are not
  // necessarily complete and may be expanded on demand.
  GuardAssignTable *m_clobber_table;

  // table of points for calls and loops which may GC.
  Vector<PPoint> *m_gc_table;

  // derived tables. these are memoization results computed on demand and
  // are thrown away when we are finished with the BlockMemory.

  // table of the known lvalue expression values at each point.
  typedef HashTable<PointValue,GuardExp,PointValue> ValueTable;
  ValueTable *m_val_table;

  // table of expression translation results at each point.
  typedef HashTable<PointTranslate,GuardExp,PointTranslate> TranslateTable;
  TranslateTable *m_translate_table;

 private:
  // helper methods for use while computing tables and the val() relation

  // create and initialize all the persistent and derived tables.
  void MakeTables();

  // sanity check a list of outgoing edges
  void CheckOutgoingEdges(const Vector<PEdge*> &outgoing);

  // compute guard and edge persistent information
  void ComputeGuard(PPoint point);
  void ComputeEdgeAssume(PEdgeAssume *edge);
  void ComputeEdgeAssign(PEdgeAssign *edge);
  void ComputeEdgeCall(PEdgeCall *edge);
  void ComputeEdgeLoop(PEdgeLoop *edge);

  // fill in assigns with the result of a single assignment from right to left
  // of the specified type. if type is a CSU then it will be split into
  // separate assignments of each field. does not get references on true bits.
  void ComputeSingleAssign(Type *type, Exp *left, Exp *right, Bit *when,
                           Vector<GuardAssign> *assigns);

  // combine each expression in target_list with its values at point to
  // fill in res. if get_value is set then the straight values at point
  // are used. if get_edge is set then the values after the edge at point
  // are used. otherwise the value at entry is used (the straight Drf/etc.)
  void TranslateExpVal(PPoint point, Exp *kind,
                       const GuardExpVector &target_list,
                       bool get_value, bool get_edge,
                       GuardExpVector *res);

  // transfer function for Drf() expressions.
  void TransferEntryDrf(Exp *lval, GuardExpVector *res);
  void TransferEdgeDrf(Exp *lval, PEdge *edge, GuardExpVector *res);

  // transfer function for Terminate() expressions.
  void TransferEntryTerminate(Exp *lval, ExpTerminate *kind,
                              GuardExpVector *res);
  void TransferEdgeTerminate(Exp *lval, ExpTerminate *kind, PEdge *edge,
                             GuardExpVector *res);

  // extra Terminate transfer when lval is clobbered by the 'clobber' exp.
  void TransferClobberTerminate(Exp *lval, ExpTerminate *kind,
                                ExpClobber *clobber, GuardExpVector *res);

  // transfer function for GCSafe() expressions.
  void TransferEntryGCSafe(Exp *lval, ExpGCSafe *kind,
			   GuardExpVector *res);
  void TransferEdgeGCSafe(Exp *lval, ExpGCSafe *kind, PEdge *edge,
			  GuardExpVector *res);

  // create a memory analysis for the specified block and backends.
  // if any of the backends are 0 then a default behavior will be
  // used for those queries (no simplification/aliasing/clobbering
  // will be performed).
  BlockMemory(BlockId *id,
              MemorySimplifyKind simplify_kind,
              MemoryAliasKind alias_kind,
              MemoryClobberKind clobber_kind);

  static HashCons<BlockMemory> g_table;
};

NAMESPACE_XGILL_END
