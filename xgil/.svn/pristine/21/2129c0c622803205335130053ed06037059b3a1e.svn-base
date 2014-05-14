
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

#include "hashtable.h"

NAMESPACE_XGILL_BEGIN

// weak cache mapping values to one another. when all references
// to an entry in the cache go away, it stays in the cache and is
// eventually removed in an LRU order. when a lookup occurs on an item
// that is not currently in the cache, an external user-supplied routine
// is called to fetch the item, possibly from external storage.
template <class T, class U, class HT>
class HashCache
{
 public:
  // interface structure for looking up items that aren't in a cache
  // or flushing changes to items being removed from a cache.
  class ExternalLookup
  {
   public:
    // looks up whatever value (if any) is associated with v, and inserts
    // it into the specified cache. may insert additional elements into the
    // cache, but must insert a value for v. this will block until
    // the operation completes.
    virtual void LookupInsert(HashCache<T,U,HT> *cache, T v) = 0;

    // called immediately after the key/value pair v/o are removed from
    // the cache. any references held on these values need to be dropped,
    // and any changes made to v/u flushed, if necessary.
    virtual void Remove(HashCache<T,U,HT> *cache, T v, U o) {}
  };

 public:
  // create a cache with the specified external lookup routine.
  // least used entries will be removed from the cache as the total
  // number of entries exceeds max_entry_count. this eviction is automatic
  // if eviction_enabled is true, manual if false (see SetLruEviction()).
  HashCache(ExternalLookup *external_lookup,
            size_t max_entry_count,
            bool eviction_enabled = true);

  // get whether this cache is empty.
  bool IsEmpty() { return m_entry_count == 0; }

  // get whether this cache contains candidates for Lru removal.
  bool HasLru()
  {
    return (m_entry_count > m_max_entry_count)
        && (m_free_begin != NULL);
  }

  // get the interface used to lookup entries not currently in the cache.
  ExternalLookup* GetExternalLookup() const { return m_external_lookup; }

  // enable or disable automatic eviction of least recently used entries
  // when the number of entries exceeds max_entry_count. if this is disabled
  // then the client needs to periodically call Clear() or RemoveLruEntries()
  // on the cache.
  void SetLruEviction(bool enabled) { m_eviction_enabled = enabled; }

  // get the object associated with v, or NULL if it doesn't exist.
  // each call to Lookup() must be followed by a call to Release().
  // may invoke the external lookup (and block) if the object associated
  // with v is not currently in the cache.
  U Lookup(T v);

  // returns whether the specified key is currently in the cache.
  // does not do an external lookup if the key is not in the cache;
  // if the key is present, it becomes the most recently used element.
  bool IsMember(T v);

  // drops a reference from an earlier call to Lookup on v.
  void Release(T v);

  // inserts a new object o to associate with v. if the object is already in
  // the cache then Remove will be called on v/o and that existing entry will
  // become the most recently used.
  void Insert(T v, U o);

  // remove all entries in this cache, except for those entries which
  // have active lookups (Release() has not yet been called on a previous
  // Lookup() for the entry).
  void Clear();

  // remove the least recently used entries, until we are under
  // the maximum the maximum entry count or run out of entries without
  // active lookups. does not do anything if the maximum entry count
  // is not exceeded.
  void RemoveLruEntries();

 private:

  // individual entry associating two objects
  struct HashEntry {
    T source;
    U target;

    // number of times this has been looked up without being released
    size_t lookups;

    // linked entry in HashBucket list
    HashEntry *next, **pprev;

    // linked entry in free list. non-NULL iff lookups == 0
    HashEntry *free_next, **free_pprev;

    HashEntry(T _source, U _target);
    ALLOC_OVERRIDE(g_alloc_HashCache);
  };

  struct HashBucket {
    // head and tail of the list of entries in this bucket
    HashEntry *e_begin, **e_pend;

    HashBucket();
    ALLOC_OVERRIDE(g_alloc_HashCache);
  };

  // routine to call when we need to get a new entry in the cache.
  ExternalLookup *m_external_lookup;

  // buckets in this table
  HashBucket *m_buckets;

  // number of buckets in this table
  size_t m_bucket_count;

  // number of HashEntry values in any bucket
  size_t m_entry_count;

  // desired maximum number of entries in this cache
  size_t m_max_entry_count;

  // whether lru eviction is enabled
  bool m_eviction_enabled;

  // linked list of all entries in the free list, without any active
  // lookups on them. entries at the beginning are the least recently used.
  HashEntry *m_free_begin, **m_free_pend;

  struct __HashEntry_BucketList
  {
    static HashEntry**  GetNext(HashEntry *o) { return &o->next; }
    static HashEntry*** GetPPrev(HashEntry *o) { return &o->pprev; }
  };

  struct __HashEntry_FreeList
  {
    static HashEntry**  GetNext(HashEntry *o) { return &o->free_next; }
    static HashEntry*** GetPPrev(HashEntry *o) { return &o->free_pprev; }
  };

 public:
  ALLOC_OVERRIDE(g_alloc_HashCache);
};

#include "hashcache_impl.h"

NAMESPACE_XGILL_END
