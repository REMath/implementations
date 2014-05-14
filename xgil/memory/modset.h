
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

// data structures and functions for modset analysis.

#include "mblock.h"
#include "callgraph.h"

NAMESPACE_XGILL_BEGIN

class BlockModset : public HashObject
{
 public:
  static int Compare(const BlockModset *mod0, const BlockModset *mod1);
  static BlockModset* Copy(const BlockModset *mod);
  static void Write(Buffer *buf, const BlockModset *mod);
  static BlockModset* Read(Buffer *buf);

  static void WriteList(Buffer *buf, const Vector<BlockModset*> &mod_list);
  static void ReadList(Buffer *buf, Vector<BlockModset*> *mod_list);

  static BlockModset* Make(BlockId *id) {
    BlockModset xmod(id);
    return g_table.Lookup(xmod);
  }

 public:
  // get the identifier of the CFG this models the modset for.
  BlockId* GetId() const { return m_id; }

  // clear all information in this modset.
  void ClearModset();

  // fill in this modset from the lvalues modified within a BlockMemory
  // and its callees. if indirect is set then includes modsets
  // for indirect callees.
  void ComputeModset(BlockMemory *mcfg, bool indirect);

  // fill in any modset information for a target of a call/loop edge.
  void ComputeModsetCall(BlockMemory *mcfg, PEdge *edge,
                         BlockId *callee, Exp *rfld_chain);

  // merge any data from omod into this modset. return true if the merged
  // modset differs from omod.
  bool MergeModset(BlockModset *omod);

  // get the modified lvalues in this modset.
  size_t GetModsetCount() const {
    return m_modset_list ? m_modset_list->Size() : 0;
  }
  const PointValue& GetModsetLval(size_t ind) const {
    Assert(ind < GetModsetCount());
    return m_modset_list->At(ind);
  }

  // add a modified lvalue to this modset.
  void AddModset(Exp *lval, Exp *kind);

  // get the direct assignments in this modset.
  size_t GetAssignCount() const {
    return m_assign_list ? m_assign_list->Size() : 0;
  }
  const GuardAssign& GetAssign(size_t ind) const {
    Assert(ind < GetAssignCount());
    return m_assign_list->At(ind);
  }

  // add an assignment to this modset.
  void AddAssign(Exp *left, Exp *right, Bit *guard);

  // whether this can trigger GC.
  bool CanGC() const { return m_can_gc; }
  void SetCanGC() { m_can_gc = true; }

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  // function/loop ID for which this contains the modset.
  BlockId *m_id;

  // list of lvalues and associated kinds in this modset.
  Vector<PointValue> *m_modset_list;

  // list of assignments this modset models completely. lvalues in this
  // list are included in m_modset_list (other than the return lvalue).
  Vector<GuardAssign> *m_assign_list;

  // may trigger a garbage collection, for GC liveness analysis.
  bool m_can_gc;

 private:
  // helper methods for modset computation.

  // add lval to this modset if appropriate. if consider_assign is set,
  // try to get a direct assignment for the lval which always holds.
  void ProcessUpdatedLval(BlockMemory *mcfg, Exp *lval, Exp *kind,
                          bool consider_assign, bool is_call);

  BlockModset(BlockId *id);

 public:
  static HashCons<BlockModset> g_table;
};

NAMESPACE_XGILL_END
