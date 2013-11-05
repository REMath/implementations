
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

// union find structure grouping solver terms (exp x frame pairs)
// into disjoint sets.

#include <imlang/exp.h>

NAMESPACE_XGILL_BEGIN

class SolverUnionFind
{
 public:
  SolverUnionFind(size_t min_bucket_count = 89);
  ~SolverUnionFind() { Clear(); }

  // gets the root expression/frame for the specified expression/frame.
  // two exps/frames are in the same disjoint set iff their root exps/frames
  // are the same.
  void Lookup(size_t frame, Exp *exp, size_t *proot_frame, Exp **proot_exp)
  {
    HashEntry *entry = LookupEntry(frame, exp);
    *proot_frame = entry->frame;
    *proot_exp = entry->exp;
  }

  // return whether frame0/exp0 and frame1/exp1 are in the same set.
  bool SameSet(size_t frame0, Exp *exp0, size_t frame1, Exp *exp1)
  {
    HashEntry *entry0 = LookupEntry(frame0, exp0);
    HashEntry *entry1 = LookupEntry(frame1, exp1);
    return entry0 == entry1;
  }

  // merge the sets containing frame0/exp0 and frame1/exp1.
  void Merge(size_t frame0, Exp *exp0, size_t frame1, Exp *exp1);

  // mark the disjoint set containing frame/exp. if this set is subsequently
  // merged with another set the merged set will be marked as well.
  void Mark(size_t frame, Exp *exp);

  // return whether there are any marked sets.
  bool HashMarked()
  {
    return m_marked_list != NULL;
  }

  // return whether the set containing frame/exp is marked.
  bool IsMarked(size_t frame, Exp *exp)
  {
    HashEntry *entry = LookupEntry(frame, exp);
    return entry->marked_next != NULL;
  }

  // clear all marked sets. the marked sets must be cleared before pushing
  // a context. popping a context will also clear any marked sets.
  void ClearMarked();

  // push a new context onto the union find's context stack. any new lookups
  // and merges will go onto this topmost stack.
  void PushContext();

  // pop the topmost context from the stack and undo the effects of all
  // lookups and merges since the corresponding PushContext.
  void PopContext();

  // clears all entries from this union find.
  void Clear();

  // print this union find to stdout. if summary_only is true then only
  // summary information is printed.
  void Print(bool summary_only = false);

 private:
  // copy constructor and assignment not allowed.
  SolverUnionFind(const SolverUnionFind&);
  SolverUnionFind& operator = (const SolverUnionFind&);

  // individual entry for an association in this union find.
  struct HashEntry {
    size_t frame;
    Exp *exp;

    // parent entry in the union find. following these transitiviely will
    // yield the root of the disjoint set this entry is in, whose parent
    // field is NULL.
    HashEntry *parent;

    // rank of this entry, equal to the number of direct, non-transitive
    // children it has (the number of sets that have been merged with it).
    size_t rank;

    // links for the bucket's list of entries.
    HashEntry *next, **pprev;

    // link for the context's list of created entries.
    HashEntry *context_lookup_next;

    // link for the context's list of merged entries.
    HashEntry *context_parent_next;

    // link for the marked disjoint sets. if this is in the list then the
    // root of this set is in the list (merges after marking a set may cause
    // multiple entries in the set to be marked). this pointer will be 0x1
    // if it is marked but is at the end of the marked list.
    HashEntry *marked_next;

    // link for the set of all entries in this disjoint set. this pointer
    // is only used during Print() methods and is NULL otherwise.
    HashEntry *set_next;

    HashEntry()
      : frame(0), exp(NULL), parent(NULL), rank(0),
        next(NULL), pprev(NULL),
        context_lookup_next(NULL), context_parent_next(NULL),
        marked_next(NULL), set_next(NULL)
    {}
  };

  struct HashBucket {
    // head and tail of the list of entries in this bucket.
    HashEntry *e_begin, **e_pend;

    HashBucket() {
      LinkedListInit<HashEntry>(&e_begin, &e_pend);
    }
  };

  // gets the entry for the specified expression/frame. if there is no entry
  // then one will be created.
  HashEntry* LookupEntry(size_t frame, Exp *exp);

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

  // allocator used for entries in this union find.
  TrackAlloc &m_alloc;

  // buckets in this union find.
  HashBucket *m_buckets;

  // number of buckets in this union find.
  size_t m_bucket_count;

  // number of entries in this union find.
  size_t m_entry_count;

  // minimum bucket count this union find will resize to.
  size_t m_min_bucket_count;

  // context information for the union find.
  struct HashContext {
    // list of entries which were created by this context.
    HashEntry *lookup_list;

    // list of merged which were performed by this context. each merge adds
    // a single parent edge to the entries. we do not do path compression,
    // so the parent edges never change otherwise and we can restore the
    // unmerged sets by deleting these parent edges.
    HashEntry *parent_list;

    HashContext()
      : lookup_list(NULL), parent_list(NULL)
    {}
  };

  // active contexts for this union find.
  Vector<HashContext> m_contexts;

  // list of marked disjoint sets.
  HashEntry *m_marked_list;

  struct __HashEntry_List
  {
    static HashEntry**  GetNext(HashEntry *o) { return &o->next; }
    static HashEntry*** GetPPrev(HashEntry *o) { return &o->pprev; }
  };
};

NAMESPACE_XGILL_END
