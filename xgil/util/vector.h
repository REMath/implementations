
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

// this is pretty much the same as std::vector.

#include <stdlib.h>
#include "assert.h"

NAMESPACE_XGILL_BEGIN

// size of built-in storage for vector elements. if the size of the
// vector is <= this it does not need any dynamic allocation.
#define VECTOR_BASE_CAPACITY 4

// extensible array with elements of type T. if T is a class/structure type
// then the default constructor and assignment operators must be defined
// to do the right thing.
template <class T>
class Vector
{
 public:

  Vector<T>()
    : m_data(m_base_data), m_count(0),
      m_capacity(VECTOR_BASE_CAPACITY)
  {}

  Vector<T>(size_t initial_count)
    : m_data(m_base_data), m_count(0),
     m_capacity(VECTOR_BASE_CAPACITY)
  {
    Resize(initial_count);
  }

  Vector<T>(const Vector<T> &o)
    : m_data(m_base_data), m_count(0),
      m_capacity(VECTOR_BASE_CAPACITY)
  {
    *this = o;
  }

  ~Vector<T>()
  {
    Clear();
  }

  Vector<T>& operator =(const Vector<T> &o)
  {
    Clear();

    if (o.m_capacity > VECTOR_BASE_CAPACITY) {
      m_capacity = o.m_capacity;
      m_data = track_new<T>(g_alloc_Vector, m_capacity);
    }

    m_count = o.m_count;
    for (size_t ind = 0; ind < m_count; ind++)
      m_data[ind] = o.m_data[ind];

    return *this;
  }

  T& At(size_t n)
  {
    Assert(n < m_count);
    return m_data[n];
  }

  const T& At(size_t n) const
  {
    Assert(n < m_count);
    return m_data[n];
  }

  T& operator [](size_t n)
  {
    Assert(n < m_count);
    return m_data[n];
  }

  const T& operator [](size_t n) const
  {
    Assert(n < m_count);
    return m_data[n];
  }

  T& Back()
  {
    Assert(m_count > 0);
    return m_data[m_count - 1];
  }

  const T& Back() const
  {
    Assert(m_count > 0);
    return m_data[m_count - 1];
  }

  bool Empty() const
  {
    return m_count == 0;
  }

  size_t Size() const
  {
    return m_count;
  }

  void PushBack(const T &v)
  {
    Assert(m_capacity != 0);

    if (m_count == m_capacity) {
      m_capacity *= 2;

      T *new_data = track_new<T>(g_alloc_Vector, m_capacity);
      for (size_t ind = 0; ind < m_count; ind++)
        new_data[ind] = m_data[ind];

      if (m_data == m_base_data) {
        for (size_t ind = 0; ind < m_count; ind++)
          m_data[ind] = T();
      }
      else {
        track_delete<T>(g_alloc_Vector, m_data);
      }
      m_data = new_data;
    }

    m_data[m_count] = v;
    m_count++;
  }

  void PopBack()
  {
    Assert(m_count >= 1);
    m_data[m_count - 1] = T();
    m_count--;
  }

  void Resize(size_t count)
  {
    while (m_count > count)
      PopBack();
    while (m_count < count)
      PushBack(T());
  }

  T* Data() const
  {
    return m_data;
  }

  void Clear()
  {
    for (size_t ind = 0; ind < m_count; ind++)
      m_data[ind] = T();
    m_count = 0;

    if (m_data != m_base_data) {
      track_delete<T>(g_alloc_Vector, m_data);
      m_data = m_base_data;
      m_capacity = VECTOR_BASE_CAPACITY;
    }
  }

  // search this vector for the specified value, using the '==' operator.
  bool Contains(T val) const
  {
    for (size_t ind = 0; ind < m_count; ind++) {
      if (m_data[ind] == val)
        return true;
    }
    return false;
  }

 private:
  T *m_data;
  size_t m_count;
  size_t m_capacity;

  // builtin storage for storing small vectors of data
  T m_base_data[VECTOR_BASE_CAPACITY];

 public:
  ALLOC_OVERRIDE(g_alloc_Vector);
};

// sorting method for a partial vector of objects. CMP contains a Compare()
// method for comparing objects. this uses quicksort.
// sorts the region [start, last>
template <class T, class CMP>
inline void SortVectorRegion(Vector<T> *pdata, size_t start, size_t last)
{
  // ignore already sorted regions.
  if (last - start <= 1)
    return;

  // bubble sort small regions.
  if (last - start <= 5) {
    bool changed;
    do {
      changed = false;
      for (size_t ind = start; ind < last - 1; ind++) {
        int res = CMP::Compare(pdata->At(ind), pdata->At(ind + 1));
        if (res > 0) {
          T tmp = pdata->At(ind);
          pdata->At(ind) = pdata->At(ind + 1);
          pdata->At(ind + 1) = tmp;
          changed = true;
        }
      }
    } while (changed);
    return;
  }

  size_t pivot_ind = (start + last) / 2;
  T pivot_value = pdata->At(pivot_ind);
  pdata->At(pivot_ind) = pdata->At(last - 1);
  pdata->At(last - 1) = pivot_value;

  // all entries in [start, less_ind> are less than the pivot value.
  size_t less_ind = start;

  for (size_t ind = start; ind < last; ind++) {
    int res = CMP::Compare(pdata->At(ind), pivot_value);
    if (res < 0) {
      T tmp = pdata->At(less_ind);
      pdata->At(less_ind) = pdata->At(ind);
      pdata->At(ind) = tmp;
      less_ind++;
    }
  }

  // swap the pivot element to its sorted position.
  pdata->At(last - 1) = pdata->At(less_ind);
  pdata->At(less_ind) = pivot_value;

  SortVectorRegion<T,CMP>(pdata, start, less_ind);
  SortVectorRegion<T,CMP>(pdata, less_ind + 1, last);
}

// sort an entire vector using SortVectorRegion.
template <class T, class CMP>
inline void SortVector(Vector<T> *pdata)
{
  SortVectorRegion<T,CMP>(pdata, 0, pdata->Size());
}

// is the specified vector sorted per SortVector?
template <class T, class CMP>
inline bool IsSortedVector(const Vector<T> &data)
{
  if (data.Size() <= 1)
    return true;

  for (size_t ind = 0; ind < data.Size() - 1; ind++) {
    int res = CMP::Compare(data[ind], data[ind + 1]);
    if (res > 0)
      return false;
  }
  return true;
}

// get the size of an optional vector, returning zero on NULL.
template <class T>
inline size_t VectorSize(const Vector<T> *data)
{
  if (data)
    return data->Size();
  return 0;
}

NAMESPACE_XGILL_END
