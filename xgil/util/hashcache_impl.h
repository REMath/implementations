
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

/////////////////////////////////////////////////////////////////////
// HashCache
/////////////////////////////////////////////////////////////////////

template <class T, class U, class HT>
HashCache<T,U,HT>::HashEntry::HashEntry(T _source, U _target)
  : source(_source), target(_target), lookups(0),
    next(NULL), pprev(NULL),
    free_next(NULL), free_pprev(NULL)
{}

template <class T, class U, class HT>
HashCache<T,U,HT>::HashBucket::HashBucket()
{
  LinkedListInit<HashEntry>(&e_begin, &e_pend);
}

template <class T, class U, class HT>
HashCache<T,U,HT>::HashCache(ExternalLookup *external_lookup,
                             size_t max_entry_count, bool eviction_enabled)
  : m_external_lookup(external_lookup),
    m_buckets(NULL), m_bucket_count(max_entry_count),
    m_entry_count(0), m_max_entry_count(max_entry_count),
    m_eviction_enabled(eviction_enabled)
{
  Assert(m_external_lookup);
  Assert(m_bucket_count != 0);

  LinkedListInit<HashEntry>(&m_free_begin, &m_free_pend);
  m_buckets = new HashBucket[m_bucket_count];
}

template <class T, class U, class HT>
U HashCache<T,U,HT>::Lookup(T v)
{
  // if we are using automatic eviction then check to see if we are above
  // the entry limit and remove any lru entries.
  if (m_eviction_enabled)
    RemoveLruEntries();

  // look for v in the existing entries

  size_t ind = HT::Hash(0, v) % m_bucket_count;
  HashBucket *bucket = &m_buckets[ind];

  HashEntry *e = bucket->e_begin;
  while (e != NULL) {
    if (e->source == v) {
      if (e->lookups == 0) {
        Assert(e->free_pprev != NULL);
        LinkedListRemove<HashEntry,__HashEntry_FreeList>(&m_free_pend, e);
      }
      e->lookups++;
      return e->target;
    }
    e = e->next;
  }

  // insert v and any associated entries into the cache.
  m_external_lookup->LookupInsert(this, v);

  // look for the new entry for v.

  ind = HT::Hash(0, v) % m_bucket_count;
  bucket = &m_buckets[ind];

  e = bucket->e_begin;
  while (e != NULL) {
    if (e->source == v) {
      Assert(e->lookups == 0);
      Assert(e->free_pprev != NULL);
      LinkedListRemove<HashEntry,__HashEntry_FreeList>(&m_free_pend, e);
      e->lookups++;
      return e->target;
    }
    e = e->next;
  }

  // entry isn't in the cache
  Assert(false);
}

template <class T, class U, class HT>
bool HashCache<T,U,HT>::IsMember(T v)
{
  size_t ind = v->Hash() % m_bucket_count;
  HashBucket *bucket = &m_buckets[ind];

  HashEntry *e = bucket->e_begin;
  while (e != NULL) {
    if (e->source == v) {
      // move to most recently used
      if (e->lookups == 0) {
        Assert(e->free_pprev != NULL);
        LinkedListRemove<HashEntry,__HashEntry_FreeList>(&m_free_pend, e);
        LinkedListInsert<HashEntry,__HashEntry_FreeList>(&m_free_pend, e);
      }

      return true;
    }
    e = e->next;
  }

  return false;
}

template <class T, class U, class HT>
void HashCache<T,U,HT>::Release(T v)
{
  size_t ind = HT::Hash(0, v) % m_bucket_count;
  HashBucket *bucket = &m_buckets[ind];

  HashEntry *e = bucket->e_begin;
  while (e != NULL) {
    if (e->source == v) {
      Assert(e->lookups != 0);
      e->lookups--;

      if (e->lookups == 0) {
        Assert(e->free_pprev == NULL);
        LinkedListInsert<HashEntry,__HashEntry_FreeList>(&m_free_pend, e);
      }
      return;
    }
    e = e->next;
  }

  // entry isn't in the cache
  Assert(false);
}

template <class T, class U, class HT>
void HashCache<T,U,HT>::Insert(T v, U o)
{
  if (IsMember(v)) {
    // call remove to dispose of the just inserted values, and return.
    m_external_lookup->Remove(this, v, o);
    return;
  }

  m_entry_count++;

  size_t ind = v->Hash() % m_bucket_count;
  HashBucket *bucket = &m_buckets[ind];

  // make the new entry and add it to the bucket and free lists.
  HashEntry *newe = new HashEntry(v, o);
  LinkedListInsert<HashEntry,__HashEntry_BucketList>(&bucket->e_pend, newe);
  LinkedListInsert<HashEntry,__HashEntry_FreeList>(&m_free_pend, newe);
}

template <class T, class U, class HT>
void HashCache<T,U,HT>::Clear()
{
  // force the max entry count to zero to ensure we remove all free entries
  size_t old_max_entry_count = m_max_entry_count;
  m_max_entry_count = 0;

  RemoveLruEntries();

  // restore the old maximum entry count
  m_max_entry_count = old_max_entry_count;
}

template <class T, class U, class HT>
void HashCache<T,U,HT>::RemoveLruEntries()
{
  while (m_entry_count > m_max_entry_count) {
    HashEntry *e = m_free_begin;
    if (e == NULL) {
      // we have more entries than permitted, but all of them are in use
      return;
    }

    // remove the entry from the free list
    LinkedListRemove<HashEntry,__HashEntry_FreeList>(&m_free_pend, e);

    // get the bucket containing this entry
    size_t ind = HT::Hash(0, e->source) % m_bucket_count;
    HashBucket *bucket = &m_buckets[ind];

    // double check to make sure we've got the right bucket
    bool found = false;
    HashEntry *xe = bucket->e_begin;
    while (xe != NULL) {
      if (xe == e) {
        found = true;
        break;
      }
      xe = xe->next;
    }
    Assert(found);

    // remove the entry from the bucket's list
    LinkedListRemove<HashEntry,__HashEntry_BucketList>(&bucket->e_pend, e);

    // notify the external lookup about the removal.
    m_external_lookup->Remove(this, e->source, e->target);

    // do the final delete
    delete e;
    m_entry_count--;
  }
}
