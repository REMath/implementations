
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

// constraint hash tables are maps from expression/frames to one or more
// other expressions/frames. these tables support the same push/pop context
// operations as regular solver hash tables, and additionally allow listeners
// to be associated with each key in the table, which will be called whenever
// entries for that key are added.

#include <imlang/exp.h>

NAMESPACE_XGILL_BEGIN

// forward declarations.
class Solver;
class ConstraintListener;
class ConstraintTable;
struct ConstraintEntry;
struct ConstraintKey;

// function pointer for constructing ConstraintListener objects.
typedef ConstraintListener* (*ConstraintListenerFn)(Solver*, ConstraintKey*);

// get the hash for an association entry between source and target.
static uint32_t GetEntryHash(FrameId source_frame, Exp *source_exp,
                             FrameId target_frame, Exp *target_exp)
{
  uint32_t hash = Hash32(source_frame, target_frame);
  if (source_exp)
    hash = Hash32(hash, source_exp->Hash());
  if (target_exp)
    hash = Hash32(hash, target_exp->Hash());
  return hash;
}

// get the hash for an association key on source.
static uint32_t GetKeyHash(FrameId source_frame, Exp *source_exp)
{
  uint32_t hash = source_frame;
  if (source_exp)
    hash = Hash32(hash, source_exp->Hash());
  return hash;
}

// forward declarations.

// key for accessing all expressions associated with a particular source,
// within some ConstraintTable. these are referred to outside
// the hashtable, and there can be pointers between keys in different tables.
struct ConstraintKey
{
  // parent table.
  ConstraintTable *table;

  // source expression in this key.
  FrameId frame;
  Exp *exp;

  // listeners owned by this key.
  Vector<ConstraintListener*> owned_listeners;

  // listeners not owned by this key which hear changes on this key.
  Vector<ConstraintListener*> parent_listeners;

  // list of entries associated with this key.
  ConstraintEntry *entries_begin;
  ConstraintEntry **entries_pend;

  // links for the bucket's list of keys.
  ConstraintKey *next, **pprev;

  ConstraintKey()
    : table(NULL), frame(0), exp(NULL), next(NULL), pprev(NULL)
  {
    LinkedListInit<ConstraintEntry>(&entries_begin, &entries_pend);
  }

  uint32_t Hash() {
    return GetKeyHash(frame, exp);
  }
};

// entry for an association between two expressions within some
// ConstraintTable.
struct ConstraintEntry
{
  // target expression in this entry.
  FrameId frame;
  Exp *exp;

  // key entry storing the source.
  ConstraintKey *key;

  // links for the bucket's list of entries.
  ConstraintEntry *next, **pprev;

  // links for the key's list of entries.
  ConstraintEntry *key_next, **key_pprev;

  ConstraintEntry()
    : frame(0), exp(NULL), key(NULL),
      next(NULL), pprev(NULL), key_next(NULL), key_pprev(NULL)
  {}

  uint32_t Hash() {
    return GetEntryHash(key->frame, key->exp, frame, exp);
  }
};

// table of associations between expressions.
class ConstraintTable
{
 public:
  ConstraintTable(const char *name, Solver *solver,
                  size_t min_bucket_count = 89);
  ~ConstraintTable();

  // add a function to construct listeners to associate with each new key
  // in this solver. the table must be empty, and these will not be cleared
  // by calling Clear().
  void RegisterListener(ConstraintListenerFn function);

  // add an association to this table between source and target. returns
  // whether the insertion was successful (there was no such existing entry).
  bool Insert(FrameId source_frame, Exp *source_exp,
              FrameId target_frame, Exp *target_exp);

  // get the key associated with source. if there is no such key, either one
  // will be created or NULL will be returned, according to force_create.
  ConstraintKey* LookupKey(FrameId source_frame, Exp *source_exp,
                           bool force_create = false);

  // adds the specified listener to the parents for the specified key,
  // and notify it of all future associations on the key. this does *not*
  // invoke the listener on existing associations on the key. the listener
  // will persist until the corresponding pop for the current context.
  void AddListener(ConstraintKey *key, ConstraintListener *listener);

  // push a new context onto the hashtable's stack. any new inserts will go
  // onto this topmost context.
  void PushContext();

  // pop the topmost context from the stack and remove all associations
  // added since the corresponding PushContext().
  void PopContext();

  // fills in keys with every key that has been added to this table.
  void GetKeys(Vector<ConstraintKey*> *keys);

  // clear all entries from this table.
  void Clear();

  // whether this table is empty.
  bool IsEmpty() const { return m_entry_count == 0; }

  // print this table to standard out.
  void Print() const;

 private:
  // copy constructor and assignment not allowed.
  ConstraintTable(const ConstraintTable&);
  ConstraintTable& operator = (const ConstraintTable&);

  // resize for a new bucket count.
  void Resize(size_t bucket_count);

  // check the bucket vs. object counts and resize if appropriate.
  void CheckBucketCount()
  {
    // use same resizing technique as HashTable::CheckBucketCount.
    if (m_bucket_count > m_min_bucket_count &&
        m_bucket_count > m_entry_count * 4)
      Resize(m_bucket_count / 2);
    else if (m_bucket_count < m_entry_count)
      Resize(m_bucket_count * 2 + 1);
  }

  struct Bucket {
    ConstraintKey *key_begin, **key_pend;
    ConstraintEntry *entry_begin, **entry_pend;

    Bucket() {
      LinkedListInit<ConstraintKey>(&key_begin, &key_pend);
      LinkedListInit<ConstraintEntry>(&entry_begin, &entry_pend);
    }
  };

  // allocator used for entries and keys in this table.
  TrackAlloc &m_alloc;

  // printable name of this table.
  const char *m_name;

  // parent solver of this table.
  Solver *m_solver;

  // functions for constructing listeners on new keys in this table.
  Vector<ConstraintListenerFn> m_listener_functions;

  // buckets with keys and entries in this table.
  Bucket *m_buckets;

  // number of buckets in this table.
  size_t m_bucket_count;

  // number of entries in this table. >= the number of keys.
  size_t m_entry_count;

  // minimum bucket count this table will resize to.
  size_t m_min_bucket_count;

  // information about a parent listener added in some context.
  struct ParentListener {
    // key the listener was added to.
    ConstraintKey *key;

    // the listener itself. this will be the last entry in the key's
    // parent_listeners list at the point where this listener is popped.
    ConstraintListener *listener;
  };

  // information about a context in this table.
  struct TableContext {
    // list of entries added for this context.
    Vector<ConstraintEntry*> entries;

    // list of parent listeners added for this context. owned listeners are
    // implicitly added with the keys themselves.
    Vector<ParentListener> listeners;

    // list of keys added for this context. the key is added before any
    // of its entries are, and will be removed after all its entries are gone.
    Vector<ConstraintKey*> keys;
  };

  // list of active contexts for this table.
  Vector<TableContext*> m_contexts;

  struct __ConstraintKey_List
  {
    static ConstraintKey**  GetNext(ConstraintKey *o) { return &o->next; }
    static ConstraintKey*** GetPPrev(ConstraintKey *o) { return &o->pprev; }
  };

  struct __ConstraintEntry_List
  {
    static ConstraintEntry**  GetNext(ConstraintEntry *o) { return &o->next; }
    static ConstraintEntry*** GetPPrev(ConstraintEntry *o) { return &o->pprev; }
  };

  struct __ConstraintEntry_KeyList
  {
    static ConstraintEntry**  GetNext(ConstraintEntry *o) { return &o->key_next; }
    static ConstraintEntry*** GetPPrev(ConstraintEntry *o) { return &o->key_pprev; }
  };
};

extern TrackAlloc g_alloc_ConstraintTable;

// listener to changes in one or more ConstraintTables.
class ConstraintListener
{
 public:
  ConstraintListener(Solver *solver, ConstraintKey *key)
    : m_solver(solver), m_key(key)
  {}

  // main virtual method for the listener visiting a newly added
  // association in some table.
  virtual void Visit(ConstraintEntry *entry) = 0;

  // run visit for every entry associated with key.
  void VisitAll(ConstraintKey *key)
  {
    ConstraintEntry *entry = key->entries_begin;
    while (entry) {
      Visit(entry);
      entry = entry->key_next;
    }
  }

 protected:
  // parent solver of the table containing the key for this listener.
  Solver *m_solver;

  // key which owns this listener.
  ConstraintKey *m_key;
};

// ConstraintListener instance constructors.
// the classes themselves are defined in constraint.cpp

// listener which fills in the transitive equality constraint table according
// to additions to the one step equality constraint table.
ConstraintListener* MakeConstraintEqualityStep(Solver *solver, ConstraintKey *key);

// listener which adds constraints on the possible values of an lvalue.
ConstraintListener* MakeConstraintLvalue(Solver *solver, ConstraintKey *key);

// listener which adds constraints relating bounds with different
// stride types on the same buffer. if there is a ubound(lval,int8)
// and a ubound(lval,int32), add a constraint:
// ubound(lval,int8) / 4 = ubound(lval,int32).
ConstraintListener* MakeConstraintBound(Solver *solver, ConstraintKey *key);

// if possible, get an expression equivalent to bound which is expressed
// in terms of old_bound.
Exp* GetBoundEquivalent(ExpBound *bound, ExpBound *old_bound);

// listener which adds constraints relating terminators on a buffer
// with reads from entries in that buffer. if there is a zterm(lval,int8)
// and a read lval[exp]*, add a constraint:
// zterm(lval,int8) == exp ==> lval[exp]* == 0
ConstraintListener* MakeConstraintTerminate(Solver *solver, ConstraintKey *key);

// listener which adds distinctness constraints on offsets for pointers which
// cannot alias.
ConstraintListener* MakeConstraintOffset(Solver *solver, ConstraintKey *key);

// listeners which add various constraints for uninterpreted unops and binops.
ConstraintListener* MakeConstraintUnintUnop(Solver *solver, ConstraintKey *key);
ConstraintListener* MakeConstraintUnintBinop(Solver *solver, ConstraintKey *key);

// listener for unconstrained binops which combines information from two
// or more binop applications.
ConstraintListener* MakeConstraintCombineBinop(Solver *solver, ConstraintKey *key);

// get any side constraints to add on the specified binop. setting complete
// gets the maximal set of constraints, otherwise only those useful for
// invariant inference are generated.
void GetBinopConstraints(ExpBinop *exp, Vector<Bit*> *bits, bool complete);

NAMESPACE_XGILL_END
