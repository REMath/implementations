
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

#include "alias.h"
#include "serial.h"
#include "mblock.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// MemoryAlias static
/////////////////////////////////////////////////////////////////////

// list of all MemoryAlias structures, indexed by their kind.
static Vector<MemoryAlias*> *g_alias_list = NULL;

MemoryAlias* MemoryAlias::Lookup(MemoryAliasKind kind)
{
  Assert(g_alias_list != NULL);

  size_t ind = (size_t) kind;
  Assert(ind < g_alias_list->Size());
  Assert(g_alias_list->At(ind) != NULL);

  return g_alias_list->At(ind);
}

void MemoryAlias::Register(MemoryAlias *alias)
{
  // this is called during static initialization so make sure
  // g_alias_list is setup properly.
  static bool initialized_alias_list = false;
  if (!initialized_alias_list) {
    g_alias_list = new Vector<MemoryAlias*>();
    initialized_alias_list = true;
  }

  size_t ind = (size_t) alias->m_kind;
  while (ind >= g_alias_list->Size())
    g_alias_list->PushBack(NULL);

  Assert(g_alias_list->At(ind) == NULL);
  g_alias_list->At(ind) = alias;
}

MemoryAlias malias_Default(MALIAS_Default);

/////////////////////////////////////////////////////////////////////
// MemoryAliasBuffer
/////////////////////////////////////////////////////////////////////

class MemoryAliasBuffer : public MemoryAlias
{
 public:
  MemoryAliasBuffer() : MemoryAlias(MALIAS_Buffer) {}

  Bit* CheckAlias(BlockMemory *mcfg, Exp *update, Exp *lval, Exp *kind)
  {
    // only computing aliasing for terminator positions.
    if (!kind || !kind->IsTerminate())
      return NULL;

    ExpTerminate *nkind = kind->AsTerminate();

    // if the type of the update is incompatible with the stride type
    // then there is no aliasing.
    Type *type = update->GetType();
    if (!type || !nkind->IsCompatibleStrideType(type))
      return NULL;

    // reject aliasing if the updated lvalue is a plain variable.
    // these can't have terminators in any meaningful way.
    if (update->IsVar())
      return NULL;

    // otherwise consider this a definite alias. we're free to overapproximate,
    // if the updated lvalue is in a different buffer then we won't be
    // able to prove anything about its offset in relation to lval.
    return Bit::MakeConstant(true);
  }
};

MemoryAliasBuffer malias_Buffer;

NAMESPACE_XGILL_END
