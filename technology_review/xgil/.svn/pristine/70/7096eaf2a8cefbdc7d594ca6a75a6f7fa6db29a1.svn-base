
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

#include <stdio.h>
#include "list.h"
#include "vector.h"
#include "timer.h"

//#define TRACK_HASHTABLE_MEMORY

NAMESPACE_XGILL_BEGIN

// this is the ELF hash function borrowed from:
// http://www.partow.net/programming/hashfunctions/
inline uint32_t ELFHash(uint32_t hash, const void *val, uint32_t len)
{
  if (val == NULL)
    Assert(len == 0);

  const uint8_t *dval = (const uint8_t*) val;
  uint32_t x = 0;

  for (uint32_t i = 0; i < len; dval++, i++) {
    hash = (hash << 4) + (*dval);
    if ((x = hash & 0xF0000000L) != 0)
      hash ^= (x >> 24);
    hash &= ~x;
  }

  return hash;
}

// general purpose hash function for a block of data.
inline uint32_t HashBlock(uint32_t hash, const void *val, uint32_t len)
{
  return ELFHash(hash, val, len);
}

// general purpose hash function for a 32-bit value.
inline uint32_t Hash32(uint32_t hash, uint32_t value)
{
  return ELFHash(hash, &value, sizeof(value));
}

// default hash function just hashes the bits in T.
template <class T>
struct DataHash
{
  static inline uint32_t Hash(uint32_t hash, T v) {
    return HashBlock(hash, (const uint8_t*) &v, sizeof(v));
  }
};

// hash function for when T is already a hash value.
struct UIntHash
{
  static inline uint32_t Hash(uint32_t hash, uint32_t v) {
    Assert(hash == 0);
    return v;
  }
};

// an association hash table between objects. the HashTable does not maintain
// references to the objects stored in its entries; clients must ensure that
// the objects will stay live for as long as the table exists.
template <class T, class U, class HT>
class HashTable
{
 public:
  HashTable<T,U,HT>(size_t min_bucket_count = 89);
  HashTable<T,U,HT>(const char *alloc_name, size_t min_bucket_count = 89);
  ~HashTable<T,U,HT>() { Clear(); }

  // hashtables cannot be copied.
  HashTable<T,U,HT>(const HashTable<T,U,HT>&) { Assert(false); }
  HashTable<T,U,HT>& operator =(const HashTable<T,U,HT>&) { Assert(false); }

  // get the vector of objects associated with o, NULL if there are none.
  // if force is true a new, empty vector will be created and returned.
  // the client is free to add new items to this vector.
  Vector<U>* Lookup(const T &o, bool force = false);

  // get the single object associated with o in this table.
  // will assert-fail if either o is not associated with any object,
  // or if it is associated with more than one object.
  U& LookupSingle(const T &o);

  // add an association between o and v in this table, equivalent to
  // Lookup(o,true)->PushBack(v). returns whether there was an existing
  // association for o.
  bool Insert(const T &o, const U &v);

  // get whether this table is empty.
  bool IsEmpty() const { return m_entry_count == 0; }

  // get the number of keys in this table.
  size_t GetEntryCount() const { return m_entry_count; }

  // remove all values associated with o from this table.
  void Remove(const T &o);

  // clears all entries from this table.
  void Clear();

  // choose an arbitrary key from this table.
  T ChooseKey() const;

  // iteration methods. hashtables support iteration, with the restrictions
  // that the hashtable cannot be modified during the iteration and a new
  // iteration cannot be started before the existing iteration finishes.

  // start a new iteration on this table.
  void ItStart();

  // return whether the iteration is finished, having traversed all entries.
  bool ItDone();

  // advance to the next entry in the iteration.
  void ItNext();

  // get the key associated with the current iteration entry.
  const T& ItKey();

  // get the values associated with the current iteration entry.
  Vector<U>& ItValues();

  // get the single value associated with the current iteration entry.
  U& ItValueSingle();

 private:
  // resize for a new bucket count.
  void Resize(size_t bucket_count);

  // check the bucket vs. object counts and resize if appropriate.
  void CheckBucketCount()
  {
    // use same resizing technique as HashCons::CheckBucketCount.
    if (m_bucket_count > m_min_bucket_count &&
        m_bucket_count > m_entry_count * 4)
      Resize(m_bucket_count / 2);
    else if (m_bucket_count < m_entry_count)
      Resize(m_bucket_count * 2 + 1);
  }

  // individual entry associating two objects.
  struct HashEntry {
    T source;
    Vector<U> target;
    HashEntry *next, **pprev;

    HashEntry();
  };

  struct HashBucket {
    // head and tail of the list of entries in this bucket.
    HashEntry *e_begin, **e_pend;

    HashBucket();
  };

#ifdef TRACK_HASHTABLE_MEMORY
  // allocator used for entries in this table.
  TrackAlloc &m_alloc;
#endif

  // buckets in this table.
  HashBucket *m_buckets;

  // number of buckets in this table.
  size_t m_bucket_count;

  // number of HashEntry values in any bucket. this is smaller than
  // the number of inserts that have been performed in cases where
  // multiple inserts have the same key.
  size_t m_entry_count;

  // minimum bucket count this table will resize to.
  size_t m_min_bucket_count;

  // entry and bucket for any active iteration.
  HashEntry *m_iter_entry;
  size_t m_iter_bucket;

  struct __HashEntry_List
  {
    static HashEntry**  GetNext(HashEntry *o) { return &o->next; }
    static HashEntry*** GetPPrev(HashEntry *o) { return &o->pprev; }
  };

 public:
  ALLOC_OVERRIDE(g_alloc_HashTable);
};

template <class T, class HT>
class HashSet
{
 public:
  HashSet<T,HT>(size_t min_bucket_count = 89)
    : m_table(min_bucket_count)
  {}

  HashSet<T,HT>(const char *alloc_name, size_t min_bucket_count = 89)
    : m_table(alloc_name, min_bucket_count)
  {}

  // is the specified element in the set?
  bool Lookup(const T &o) {
    return m_table.Lookup(o) != NULL;
  }

  // insert the specified element into the set. return value is whether the
  // element was previously in the set.
  bool Insert(const T &o) {
    Vector<char> *entries = m_table.Lookup(o, true);
    if (entries->Empty()) {
      entries->PushBack(0);
      return false;
    }
    else {
      return true;
    }
  }

  // there are no entries in this table.
  bool IsEmpty() const {
    return m_table.IsEmpty();
  }

  // clears all entries from this set.
  void Clear() {
    m_table.Clear();
  }

  // iteration methods for the elements of this set, as for a hashtable.

  void ItStart() { m_table.ItStart(); }
  bool ItDone() { return m_table.ItDone(); }
  void ItNext() { m_table.ItNext(); }
  const T& ItKey() { return m_table.ItKey(); }

 private:
  HashTable<T,char,HT> m_table;
};

// macro with the for loop header for iterating through a HashTable or HashSet.
#define HashIterate(TABLE)                                         \
  for ((TABLE).ItStart(); !(TABLE).ItDone(); (TABLE).ItNext())

// ditto for a HashTable or HashSet pointer.
#define HashIteratePtr(TABLE)                                      \
  for ((TABLE)->ItStart(); !(TABLE)->ItDone(); (TABLE)->ItNext())

#include "hashtable_impl.h"

NAMESPACE_XGILL_END
