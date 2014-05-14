
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
// HashTable
/////////////////////////////////////////////////////////////////////

template <class T, class U, class HT>
HashTable<T,U,HT>::HashEntry::HashEntry()
  : source(), next(NULL), pprev(NULL)
{}

template <class T, class U, class HT>
HashTable<T,U,HT>::HashBucket::HashBucket()
{
  LinkedListInit<HashEntry>(&e_begin, &e_pend);
}

template <class T, class U, class HT>
HashTable<T,U,HT>::HashTable(size_t min_bucket_count)
  :
#ifdef TRACK_HASHTABLE_MEMORY
    m_alloc(g_alloc_HashTable),
#endif
    m_buckets(NULL),
    m_bucket_count(0), m_entry_count(0),
    m_min_bucket_count(min_bucket_count),
    m_iter_entry(NULL), m_iter_bucket(0)
{
  // we're not allocating until the first lookup occurs.
  Assert(min_bucket_count != 0);
}

template <class T, class U, class HT>
HashTable<T,U,HT>::HashTable(const char *alloc_name, size_t min_bucket_count)
  :
#ifdef TRACK_HASHTABLE_MEMORY
    m_alloc(LookupAlloc(alloc_name)),
#endif
    m_buckets(NULL),
    m_bucket_count(0), m_entry_count(0),
    m_min_bucket_count(min_bucket_count),
    m_iter_entry(NULL), m_iter_bucket(0)
{
  // ditto.
  Assert(min_bucket_count != 0);
}

template <class T, class U, class HT>
Vector<U>* HashTable<T,U,HT>::Lookup(const T &o, bool force)
{
  Assert(!m_iter_entry);

  if (m_bucket_count == 0) {
    Assert(m_buckets == NULL);
    Resize(m_min_bucket_count);
  }
  else {
    // need to do any resizing first to avoid invalidating bucket pointers.
    CheckBucketCount();
  }

  size_t ind = HT::Hash(0, o) % m_bucket_count;
  HashBucket *bucket = &m_buckets[ind];

  HashEntry *e = bucket->e_begin;
  while (e != NULL) {
    if (e->source == o)
      return &e->target;
    e = e->next;
  }

  if (force) {
    m_entry_count++;

    HashEntry *new_e =
#ifdef TRACK_HASHTABLE_MEMORY
      track_new_single<HashEntry>(m_alloc);
#else
      new HashEntry();
#endif
    new_e->source = o;

    LinkedListInsert<HashEntry,__HashEntry_List>(&bucket->e_pend, new_e);
    return &new_e->target;
  }
  else {
    return NULL;
  }
}

template <class T, class U, class HT>
U& HashTable<T,U,HT>::LookupSingle(const T &o)
{
  Vector<U> *list = Lookup(o, false);
  Assert(list != NULL);
  Assert(list->Size() == 1);

  return list->At(0);
}

template <class T, class U, class HT>
bool HashTable<T,U,HT>::Insert(const T &o, const U &v)
{
  Vector<U> *array = Lookup(o, true);
  array->PushBack(v);

  // if there was already an association there are at least two entries now.
  return (array->Size() >= 2);
}

template <class T, class U, class HT>
void HashTable<T,U,HT>::Remove(const T &o)
{
  Assert(!m_iter_entry);

  size_t ind = HT::Hash(0, o) % m_bucket_count;
  HashBucket *bucket = &m_buckets[ind];

  HashEntry *e = bucket->e_begin;
  while (e != NULL) {
    if (e->source == o)
      break;
    e = e->next;
  }

  if (e != NULL) {
    LinkedListRemove<HashEntry,__HashEntry_List>(&bucket->e_pend, e);
#ifdef TRACK_HASHTABLE_MEMORY
    track_delete_single<HashEntry>(m_alloc, e);
#else
    delete e;
#endif
    m_entry_count--;
    CheckBucketCount();
  }
}

template <class T, class U, class HT>
void HashTable<T,U,HT>::Clear()
{
  Assert(!m_iter_entry);

  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    HashBucket *bucket = &m_buckets[ind];

    while (bucket->e_begin != NULL) {
      HashEntry *e = bucket->e_begin;
      LinkedListRemove<HashEntry,__HashEntry_List>(&bucket->e_pend, e);
#ifdef TRACK_HASHTABLE_MEMORY
      track_delete_single<HashEntry>(m_alloc, e);
#else
      delete e;
#endif
    }
  }

  if (m_buckets != NULL) {
#ifdef TRACK_HASHTABLE_MEMORY
    track_delete<HashBucket>(m_alloc, m_buckets);
#else
    delete[] m_buckets;
#endif
    m_buckets = NULL;
  }

  m_bucket_count = 0;
  m_entry_count = 0;
}

template <class T, class U, class HT>
T HashTable<T,U,HT>::ChooseKey() const
{
  Assert(!IsEmpty());

  // get a random index to start at. RAND_MAX might be less than
  // the number of buckets in the table.
  size_t start_ind = rand() % m_bucket_count;

  for (size_t ind = start_ind; ind < m_bucket_count; ind++) {
    HashBucket *bucket = &m_buckets[ind];
    if (bucket->e_begin != NULL)
      return bucket->e_begin->source;
  }

  for (size_t ind = 0; ind < start_ind; ind++) {
    HashBucket *bucket = &m_buckets[ind];
    if (bucket->e_begin != NULL)
      return bucket->e_begin->source;
  }

  Assert(false);
  return T();
}

template <class T, class U, class HT>
void HashTable<T,U,HT>::ItStart()
{
  Assert(!m_iter_entry);

  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    HashEntry *entry = m_buckets[ind].e_begin;
    if (entry) {
      m_iter_entry = entry;
      m_iter_bucket = ind;
      return;
    }
  }
}

template <class T, class U, class HT>
bool HashTable<T,U,HT>::ItDone()
{
  return (m_iter_entry == NULL);
}

template <class T, class U, class HT>
void HashTable<T,U,HT>::ItNext()
{
  Assert(m_iter_entry);

  if (m_iter_entry->next) {
    // there are more entries for the active bucket.
    m_iter_entry = m_iter_entry->next;
    return;
  }

  for (size_t ind = m_iter_bucket + 1; ind < m_bucket_count; ind++) {
    HashEntry *entry = m_buckets[ind].e_begin;
    if (entry) {
      m_iter_entry = entry;
      m_iter_bucket = ind;
      return;
    }
  }

  m_iter_entry = NULL;
  m_iter_bucket = 0;
}

template <class T, class U, class HT>
const T& HashTable<T,U,HT>::ItKey()
{
  Assert(m_iter_entry);
  return m_iter_entry->source;
}

template <class T, class U, class HT>
Vector<U>& HashTable<T,U,HT>::ItValues()
{
  Assert(m_iter_entry);
  return m_iter_entry->target;
}

template <class T, class U, class HT>
U& HashTable<T,U,HT>::ItValueSingle()
{
  Assert(m_iter_entry);
  Assert(m_iter_entry->target.Size() == 1);
  return m_iter_entry->target[0];
}

template <class T, class U, class HT>
void HashTable<T,U,HT>::Resize(size_t bucket_count)
{
  Assert(bucket_count >= m_min_bucket_count);
  HashBucket *buckets =
#ifdef TRACK_HASHTABLE_MEMORY
    track_new<HashBucket>(m_alloc, bucket_count);
#else
    new HashBucket[bucket_count];
#endif

  for (size_t ind = 0; ind < m_bucket_count; ind++) {
    HashBucket *bucket = &m_buckets[ind];

    while (bucket->e_begin != NULL) {
      HashEntry *e = bucket->e_begin;
      LinkedListRemove<HashEntry,__HashEntry_List>(&bucket->e_pend, e);

      size_t nind = HT::Hash(0, e->source) % bucket_count;
      HashBucket *nbucket = &buckets[nind];
      LinkedListInsert<HashEntry,__HashEntry_List>(&nbucket->e_pend, e);
    }
  }

  if (m_buckets != NULL) {
#ifdef TRACK_HASHTABLE_MEMORY
    track_delete<HashBucket>(m_alloc, m_buckets);
#else
    delete[] m_buckets;
#endif
    m_buckets = NULL;
  }

  m_buckets = buckets;
  m_bucket_count = bucket_count;
}
