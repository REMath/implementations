
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

// interface for BlockMemory to simplify portions of the memory information.

#include <imlang/block.h>

NAMESPACE_XGILL_BEGIN

// kinds of simplification backends. each kind is associated uniquely with
// a particular statically allocated backend.
enum MemorySimplifyKind {
  // never simplify anything.
  MSIMP_Default = 0,

  // simplify any expression with two or more values.
  MSIMP_Maximal = 1,

  // simplify any non-pointer expression with two or more values.
  MSIMP_Scalar = 2,

  // simplify when there are at least 4 values for an expression.
  MSIMP_Group4 = 3
};

// forward declarations from block.h
struct GuardExp;

class MemorySimplify
{
 public:
  // get the backend associated with the specified kind.
  static MemorySimplify* Lookup(MemorySimplifyKind kind);

 public:
  MemorySimplify(MemorySimplifyKind kind)
    : m_kind(kind)
  {
    Register(this);
  }

  MemorySimplifyKind Kind() const { return m_kind; }

  // return whether the specified list of guarded expressions should be
  // simplified to a single unconstrained value. will only be called if
  // there is at least one expression in the list.
  virtual bool SimplifyValues(const Vector<GuardExp> &exps)
  {
    return false;
  }

  // return whether the specified bit should be simplified to a single
  // unconstrained bit.
  virtual bool SimplifyBit(Bit *bit)
  {
    return false;
  }

 private:
  MemorySimplifyKind m_kind;

  // register a new backend.
  static void Register(MemorySimplify *simp);
};

NAMESPACE_XGILL_END
