
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

// interface for BlockMemory to ask aliasing queries on particular traces.

#include <imlang/block.h>

NAMESPACE_XGILL_BEGIN

// forward declarations.
class BlockMemory;

// kinds of aliasing backends. each kind is associated uniquely with
// a particular statically allocated backend.
enum MemoryAliasKind {
  // never any aliasing.
  MALIAS_Default = 0,

  // determine aliasing for buffer terminators, no aliasing otherwise.
  MALIAS_Buffer = 1
};

class MemoryAlias
{
 public:
  // get the backend associated with the specified kind.
  static MemoryAlias* Lookup(MemoryAliasKind kind);

 public:
  MemoryAlias(MemoryAliasKind kind)
    : m_kind(kind)
  {
    Register(this);
  }

  MemoryAliasKind Kind() const { return m_kind; }

  // get the condition where writing to update can change the value of lval
  // according to the specified kind. returns NULL if there can be no alias.
  virtual Bit* CheckAlias(BlockMemory *mcfg,
                          Exp *update, Exp *lval, Exp *kind)
  {
    return NULL;
  }

 private:
  MemoryAliasKind m_kind;

  // register a new backend.
  static void Register(MemoryAlias *alias);
};

NAMESPACE_XGILL_END
