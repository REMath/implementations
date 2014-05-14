
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

#include "simplify.h"
#include "mblock.h"
#include "serial.h"

NAMESPACE_XGILL_BEGIN

// cutoff for the maximum TermCount() of a single expression before reducing
// to a ExpVal even if there is a single possibility. enormous expressions
// can gum up the memory analysis.
#define EXP_TERM_CUTOFF 5

// cutoff for the maximum size of a bit before reducing to an ExpGuard.
#define BIT_CUTOFF 15

/////////////////////////////////////////////////////////////////////
// MemorySimplify static
/////////////////////////////////////////////////////////////////////

// list of all MemorySimplify structures, indexed by their kind.
static Vector<MemorySimplify*> *g_simplify_list = NULL;

MemorySimplify* MemorySimplify::Lookup(MemorySimplifyKind kind)
{
  Assert(g_simplify_list != NULL);

  size_t ind = (size_t) kind;
  Assert(ind < g_simplify_list->Size());
  Assert(g_simplify_list->At(ind) != NULL);

  return g_simplify_list->At(ind);
}

void MemorySimplify::Register(MemorySimplify *simp)
{
  // this is called during static initialization so make sure
  // g_simplify_list is setup properly.
  static bool initialized_simplify_list = false;
  if (!initialized_simplify_list) {
    g_simplify_list = new Vector<MemorySimplify*>();
    initialized_simplify_list = true;
  }

  size_t ind = (size_t) simp->m_kind;
  while (ind >= g_simplify_list->Size())
    g_simplify_list->PushBack(NULL);

  Assert(g_simplify_list->At(ind) == NULL);
  g_simplify_list->At(ind) = simp;
}

MemorySimplify msimp_Default(MSIMP_Default);

/////////////////////////////////////////////////////////////////////
// MemorySimplifyMaximal
/////////////////////////////////////////////////////////////////////

class MemorySimplifyMaximal : public MemorySimplify
{
 public:
  MemorySimplifyMaximal() : MemorySimplify(MSIMP_Maximal) {}

  bool SimplifyValues(const Vector<GuardExp> &exps)
  {
    if (exps.Size() > 1 || exps[0].exp->TermCount() > EXP_TERM_CUTOFF)
      return true;
    return false;
  }

  bool SimplifyBit(Bit *bit)
  {
    if (bit->Size() > BIT_CUTOFF)
      return true;
    return false;
  }
};

MemorySimplifyMaximal msimp_Maximal;

/////////////////////////////////////////////////////////////////////
// MemorySimplifyPointer
/////////////////////////////////////////////////////////////////////

class MemorySimplifyScalar : public MemorySimplify
{
 public:
  MemorySimplifyScalar() : MemorySimplify(MSIMP_Scalar) {}

  bool SimplifyValues(const Vector<GuardExp> &exps)
  {
    // check if the exps indicate the address of a memory location,
    // e.g. this is a list of values for a pointer.
    if (exps.Size() > 1) {
      for (size_t ind = 0; ind < exps.Size(); ind++) {
        if (exps[ind].exp->GetType() != NULL)
          return false;
      }
    }

    if (exps.Size() > 1 || exps[0].exp->TermCount() > EXP_TERM_CUTOFF)
      return true;
    return false;
  }

  bool SimplifyBit(Bit *bit)
  {
    if (bit->Size() > BIT_CUTOFF)
      return true;
    return false;
  }
};

MemorySimplifyScalar msimp_Scalar;

/////////////////////////////////////////////////////////////////////
// MemorySimplifyGroup4
/////////////////////////////////////////////////////////////////////

class MemorySimplifyGroup4 : public MemorySimplify
{
 public:
  MemorySimplifyGroup4() : MemorySimplify(MSIMP_Group4) {}

  bool SimplifyValues(const Vector<GuardExp> &exps)
  {
    return exps.Size() >= 4;
  }

  bool SimplifyBit(Bit *bit)
  {
    if (bit->Size() > BIT_CUTOFF)
      return true;
    return false;
  }
};

MemorySimplifyGroup4 msimp_Group4;

NAMESPACE_XGILL_END
