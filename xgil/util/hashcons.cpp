
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

#include <stdlib.h>
#include "hashcons.h"
#include "buffer.h"

NAMESPACE_XGILL_BEGIN

TrackAlloc g_alloc_HashCons("HashCons");
TrackAlloc g_alloc_HashObject("HashObject");

/////////////////////////////////////////////////////////////////////
// HashObject
/////////////////////////////////////////////////////////////////////

void HashObject::Dbp() const
{
  Print(cout);
  cout << endl << flush;
}

void HashObject::ToString(Buffer *buf) const
{
  BufferOutStream out(buf);
  Print(out);
  out << '\0';
}

bool HashObject::EqualsString(const char *str) const
{
  Buffer string_buf;
  ToString(&string_buf);
  return (strcmp(str, (const char*) string_buf.base) == 0);
}

struct __HashObject_List
{
  static HashObject**  GetNext(HashObject *o) { return &o->m_next; }
  static HashObject*** GetPPrev(HashObject *o) { return &o->m_pprev; }
};

void HashObject::HashInsert(HashObject ***ppend, size_t *pcount)
{
  Assert(m_ppend == NULL && m_pcount == NULL);

  m_ppend = ppend;
  LinkedListInsert<HashObject,__HashObject_List>(m_ppend, this);

  m_pcount = pcount;
  (*m_pcount)++;
}

void HashObject::HashRemove()
{
  Assert(m_ppend != NULL && m_pcount != NULL);

  LinkedListRemove<HashObject,__HashObject_List>(m_ppend, this);
  m_ppend = NULL;

  (*m_pcount)--;
  m_pcount = NULL;
}

/////////////////////////////////////////////////////////////////////
// HashCons
/////////////////////////////////////////////////////////////////////

HashCons<HashObject> *g_hashcons_list;

void RegisterHashCons(HashCons<HashObject> *hash)
{
  // this function is called during static initialization so make
  // sure that g_hashcons_list is initialized before we do anything to it.
  static bool initialized_hashcons_list = false;
  if (!initialized_hashcons_list) {
    g_hashcons_list = NULL;
    initialized_hashcons_list = true;
  }

  hash->m_hash_next = g_hashcons_list;
  g_hashcons_list = hash;
}

NAMESPACE_XGILL_END
