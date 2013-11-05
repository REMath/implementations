
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

// functions and structures for tracking amount of allocated space.

#include <new>

#include "stream.h"

// use the custom allocator for counting allocations for release builds.
// for debug builds we want valgrind to work without getting confused.
// this is currently disabled as it does not work in all configurations. fix?
//#ifndef DEBUG
//#define USE_COUNT_ALLOCATOR
//#endif

// total number of heap-allocated bytes. this is a delta from the
// last time ResetAllocs() was called, so it could be negative
// (which will be printed as a very large number).
extern size_t g_alloc_total;

// reset all allocation data to zero. before this is called, PrintAllocs()
// will produce garbage. after this is called, PrintAllocs() shows an
// allocation delta from the most recent call to ResetAllocs(). this is
// typically called after entry to main, so that the allocations printed
// do not reflect any allocation performed during static initialization
// (this amount is typically small).
void ResetAllocs();

// print information about heap-allocated memory.
void PrintAllocs();

struct TrackAlloc
{
  const char *name;
  size_t alloc_total;
  TrackAlloc *next;

  TrackAlloc(const char *_name);
};

// gets the allocator associated with the specified name, creating
// a new one if one does not exist. the name should not be shared
// with an allocator that is statically allocated (a global variable).
TrackAlloc& LookupAlloc(const char *name);

#ifdef USE_COUNT_ALLOCATOR

inline void* operator new(size_t size)
{
  size_t nsize = size + 4;
  void *pbase = malloc(nsize);
  *((uint32_t*)pbase) = nsize;
  g_alloc_total += nsize;
  return ((uint8_t*)pbase) + 4;
}

inline void* operator new[](size_t size)
{
  size_t nsize = size + 4;
  void *pbase = malloc(nsize);
  *((uint32_t*)pbase) = nsize;
  g_alloc_total += nsize;
  return ((uint8_t*)pbase) + 4;
}

inline void operator delete(void *p)
{
  if (p) {
    void *pbase = ((uint8_t*)p) - 4;
    g_alloc_total -= *((uint32_t*)pbase);
    free(pbase);
  }
}

inline void operator delete[](void *p)
{
  if (p) {
    void *pbase = ((uint8_t*)p) - 4;
    g_alloc_total -= *((uint32_t*)pbase);
    free(pbase);
  }
}

// replacement for new when allocating a single primitive data or
// other object which should be tracked witha lloc.
template <class T>
inline T* track_new_single(TrackAlloc &alloc) {
  T *res = new T();
  void *pbase = ((uint8_t*)res) - 4;
  alloc.alloc_total += *((uint32_t*)pbase);
  return res;
}

// replacement for delete when deleting an object allocated
// with track_new_single.
template <class T>
inline void track_delete_single(TrackAlloc &alloc, T *val) {
  if (val) {
    void *pbase = ((uint8_t*)val) - 4;
    alloc.alloc_total -= *((uint32_t*)pbase);
    delete val;
  }
}

// replacement for new[] when allocating an array of primitive data
// or other objects which should be tracked with alloc.
template <class T>
inline T* track_new(TrackAlloc &alloc, size_t count) {
  T *res = new T[count];
  void *pbase = ((uint8_t*)res) - 4;
  alloc.alloc_total += *((uint32_t*)pbase);
  return res;
}

// replacement for delete[] when deleting an array allocated with track_new.
template <class T>
inline void track_delete(TrackAlloc &alloc, T *val) {
  if (val) {
    void *pbase = ((uint8_t*)val) - 4;
    alloc.alloc_total -= *((uint32_t*)pbase);
    delete[] val;
  }
}

// override the new/delete operators for a class to use the specified ALLOC.
#define ALLOC_OVERRIDE(ALLOC)                           \
  static void* operator new (size_t size) {             \
    size_t nsize = size + 4;                            \
    void *pbase = malloc(nsize);                        \
    *((uint32_t*)pbase) = nsize;                        \
    g_alloc_total += nsize;                             \
    (ALLOC).alloc_total += nsize;                       \
    return ((uint8_t*)pbase) + 4;                       \
  }                                                     \
  static void* operator new[] (size_t size) {           \
    size_t nsize = size + 4;                            \
    void *pbase = malloc(nsize);                        \
    *((uint32_t*)pbase) = nsize;                        \
    g_alloc_total += nsize;                             \
    (ALLOC).alloc_total += nsize;                       \
    return ((uint8_t*)pbase) + 4;                       \
  }                                                     \
  static void operator delete (void *p) {               \
    if (p) {                                            \
      void *pbase = ((uint8_t*)p) - 4;                  \
      size_t osize = *((uint32_t*)pbase);               \
      g_alloc_total -= osize;                           \
      (ALLOC).alloc_total -= osize;                     \
      free(pbase);                                      \
    }                                                   \
  }                                                     \
  static void operator delete[] (void *p) {             \
    if (p) {                                            \
      void *pbase = ((uint8_t*)p) - 4;                  \
      size_t osize = *((uint32_t*)pbase);               \
      g_alloc_total -= osize;                           \
      (ALLOC).alloc_total -= osize;                     \
      free(pbase);                                      \
    }                                                   \
  }

#else // USE_COUNT_ALLOCATOR

#define ALLOC_OVERRIDE(alloc)

template <class T>
inline T* track_new_single(TrackAlloc &alloc) {
  return new T();
}

template <class T>
inline void track_delete_single(TrackAlloc &alloc, T *val) {
  delete val;
}

template <class T>
inline T* track_new(TrackAlloc &alloc, size_t count) {
  return new T[count];
}

// replacement for delete[] when deleting an array allocated with track_new.
template <class T>
inline void track_delete(TrackAlloc &alloc, T *val) {
  delete[] val;
}

#endif // USE_COUNT_ALLOCATOR

// allocators provided for other utility headers which do not have
// object files.

extern TrackAlloc g_alloc_Vector;
extern TrackAlloc g_alloc_HashCache;
extern TrackAlloc g_alloc_HashTable;
