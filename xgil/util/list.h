
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

#include "assert.h"

NAMESPACE_XGILL_BEGIN

// unidirectional Linked List declarations.
// these have two pointers for a next and 'last next' entry,
// to simplify insert/delete handling but only allow traversal
// of the list in one direction.

template <class T>
inline void LinkedListInit(T **phead, T ***pend)
{
  *phead = NULL;
  *pend = phead;
}

// insert value at end of the list.
template <class T, class XT>
inline void LinkedListInsert(T ***pend, T *value)
{
  T **pnext = XT::GetNext(value);
  T ***pprev = XT::GetPPrev(value);
  *pnext = **pend;
  *pprev = *pend;
  **pend = value;
  *pend = pnext;
}

// insert value at head of the list.
template <class T, class XT>
inline void LinkedListInsertHead(T **phead, T *value)
{
  T **pnext = XT::GetNext(value);
  T ***pprev = XT::GetPPrev(value);
  *pnext = *phead;
  *pprev = phead;
  if (*phead != NULL) {
    T ***npprev = XT::GetPPrev(*phead);
    *npprev = pnext;
  }
  *phead = value;
}

template <class T, class XT>
inline void LinkedListRemove(T ***pend, T *value)
{
  T **pnext = XT::GetNext(value);
  T ***pprev = XT::GetPPrev(value);
  if (*pnext != NULL) {
    T ***npprev = XT::GetPPrev(*pnext);
    *npprev = *pprev;
  }
  else {
    *pend = *pprev;
  }
  **pprev =  *pnext;
  *pnext = NULL;
  *pprev = NULL;
}

template <class T,class XT>
inline void LinkedListCheckIntegrity(T **begin, T **pend)
{
  T **prev = begin;
  T *value = *prev;
  while (value != NULL) {
    Assert(*XT::GetPPrev(value) == prev);
    prev = XT::GetNext(value);
    value = *prev;
  }
  Assert(pend == prev);
}

NAMESPACE_XGILL_END
