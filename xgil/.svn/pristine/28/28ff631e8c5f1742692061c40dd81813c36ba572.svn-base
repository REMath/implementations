
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

#include "union_find.h"

NAMESPACE_XGILL_BEGIN

TrackAlloc g_alloc_SolverUnionFind("SolverUnionFind");

SolverUnionFind::SolverUnionFind(size_t min_bucket_count)
  : m_alloc(g_alloc_SolverUnionFind),
    m_buckets(NULL), m_bucket_count(0), m_entry_count(0),
    m_min_bucket_count(min_bucket_count), m_marked_list(NULL)
{
  // not allocating until the first lookup.
  Assert(m_min_bucket_count);
}

SolverUnionFind::HashEntry* SolverUnionFind::LookupEntry(size_t frame, Exp *exp)
{
  if (m_bucket_count == 0) {
    Assert(m_buckets == NULL);
    Resize(m_min_bucket_count);
  }
  else {
    CheckBucketCount();
  }

  size_t ind = Hash32(frame, exp->Hash()) % m_bucket_count;
  HashBucket *bucket = &m_buckets[ind];

  HashEntry *e = bucket->e_begin;
  while (e != NULL) {
    if (e->exp == exp && e->frame == frame) {
      while (e->parent)
        e = e->parent;
      return e;
    }
    e = e->next;
  }

  m_entry_count++;

  HashEntry *new_e = track_new_single<HashEntry>(m_alloc);
  new_e->exp = exp;
  new_e->frame = frame;

  LinkedListInsert<HashEntry,__HashEntry_List>(&bucket->e_pend, new_e);

  // add this to the topmost context if there is one.
  if (!m_contexts.Empty()) {
    HashContext &context = m_contexts.Back();
    new_e->context_lookup_next = context.lookup_list;
    context.lookup_list = new_e;
  }

  return new_e;
}

void SolverUnionFind::Merge(size_t frame0, Exp *exp0,
                            size_t frame1, Exp *exp1)
{
  HashEntry *entry0 = LookupEntry(frame0, exp0);
  HashEntry *entry1 = LookupEntry(frame1, exp1);

  if (entry0 == entry1)
    return;

  Assert(entry0->parent == NULL);
  Assert(entry1->parent == NULL);

  HashEntry *parent;
  HashEntry *child;
  if (entry0->rank > entry1->rank) {
    parent = entry0;
    child = entry1;
  }
  else {
    parent = entry1;
    child = entry0;
  }

  child->parent = parent;
  parent->rank++;

  // if the child was marked then mark the parent too.
  if (child->marked_next && !parent->marked_next) {
    parent->marked_next = child->marked_next;
    child->marked_next = parent;
  }

  // add this to the topmost context if there is one.
  if (!m_contexts.Empty()) {
    HashContext &context = m_contexts.Back();
    child->context_parent_next = context.parent_list;
    context.parent_list = child;
  }
}

void SolverUnionFind::Mark(size_t frame, Exp *exp)
{
  HashEntry *entry = LookupEntry(frame, exp);
  if (m_marked_list) {
    entry->marked_next = m_marked_list;
    m_marked_list = entry;
  }
  else {
    entry->marked_next = (HashEntry*) 1;
    m_marked_list = entry;
  }
}

void SolverUnionFind::ClearMarked()
{
  if (m_marked_list) {
    HashEntry *entry = m_marked_list;
    m_marked_list = NULL;
    while (entry != (HashEntry*) 1) {
      Assert(entry);
      HashEntry *next = entry->marked_next;
      entry->marked_next = NULL;
      entry = next;
    }
  }
}

void SolverUnionFind::PushContext()
{
  Assert(m_marked_list == NULL);
  m_contexts.PushBack(HashContext());
}

void SolverUnionFind::PopContext()
{
  ClearMarked();

  HashContext context = m_contexts.Back();
  m_contexts.PopBack();

  // disconnect all parent links added during merging for this context.

  HashEntry *child = context.parent_list;
  while (child) {
    Assert(child->parent);
    Assert(child->parent->rank);

    child->parent->rank--;
    child->parent = NULL;

    child = child->context_parent_next;
  }

  // delete all entries created for this context.

  HashEntry *lookup = context.lookup_list;
  while (lookup) {
    HashEntry *remove = lookup;
    lookup = lookup->context_lookup_next;

    // find the bucket the entry is in and disconnect the entry.
    size_t ind = Hash32(remove->frame, remove->exp->Hash()) % m_bucket_count;
    HashBucket *bucket = &m_buckets[ind];

    LinkedListRemove<HashEntry,__HashEntry_List>(&bucket->e_pend, remove);

    track_delete_single<HashEntry>(m_alloc, remove);
    m_entry_count--;
  }
}

void SolverUnionFind::Clear()
{
  ClearMarked();

  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    HashBucket *bucket = &m_buckets[ind];

    while (bucket->e_begin != NULL) {
      HashEntry *e = bucket->e_begin;

      LinkedListRemove<HashEntry,__HashEntry_List>(&bucket->e_pend, e);

      track_delete_single<HashEntry>(m_alloc, e);
      m_entry_count--;
    }
  }

  if (m_buckets != NULL) {
    track_delete<HashBucket>(m_alloc, m_buckets);
    m_buckets = NULL;
  }

  Assert(m_entry_count == 0);
  m_bucket_count = 0;
  m_contexts.Clear();
}

void SolverUnionFind::Resize(size_t bucket_count)
{
  Assert(bucket_count >= m_min_bucket_count);
  HashBucket *buckets = track_new<HashBucket>(m_alloc, bucket_count);

  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    HashBucket *bucket = &m_buckets[ind];

    while (bucket->e_begin != NULL) {
      HashEntry *e = bucket->e_begin;
      LinkedListRemove<HashEntry,__HashEntry_List>(&bucket->e_pend, e);

      size_t nind = Hash32(e->frame, e->exp->Hash()) % bucket_count;
      HashBucket *nbucket = &buckets[nind];
      LinkedListInsert<HashEntry,__HashEntry_List>(&nbucket->e_pend, e);
    }
  }

  if (m_buckets != NULL)
    track_delete<HashBucket>(m_alloc, m_buckets);

  m_buckets = buckets;
  m_bucket_count = bucket_count;
}

void SolverUnionFind::Print(bool summary_only)
{
  logout << "UnionFind:" << endl;

  // fill in the set_next links for grouping entries by their disjoint set.

  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    HashEntry *e = m_buckets[ind].e_begin;

    while (e != NULL) {
      if (e->parent == NULL) {
        e = e->next;
        continue;
      }

      Assert(e->set_next == NULL);

      HashEntry *root = e;
      while (root->parent)
        root = root->parent;

      e->set_next = root->set_next;
      root->set_next = e;

      e = e->next;
    }
  }

  // calculate information about the disjoint sets, and print them
  // out if desired. also clear out the set_next links.

  // number of disjoint sets in the union find.
  size_t set_count = 0;

  // maximum size of a disjoint set in the union find.
  size_t max_size = 0;

  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    HashEntry *root = m_buckets[ind].e_begin;

    while (root != NULL) {
      if (root->parent) {
        root = root->next;
        continue;
      }

      // root is the root of a disjoint set.
      set_count++;

      size_t set_size = 0;

      if (!summary_only)
        logout << "  Disjoint " << set_count << ":" << endl;

      HashEntry *member = root;
      while (member) {
        if (!summary_only)
          logout << "    " << member->frame << " " << member->exp << endl;
        set_size++;

        // advance to the next member in the set and clear the set_next.
        HashEntry *next = member->set_next;
        member->set_next = NULL;
        member = next;
      }

      if (set_size > max_size)
        max_size = set_size;

      root = root->next;
    }
  }

  logout << "  Entries: " << m_entry_count << endl;
  logout << "  Sets: " << set_count << endl;
  logout << "  Maximum Size: " << max_size << endl;
}

NAMESPACE_XGILL_END
