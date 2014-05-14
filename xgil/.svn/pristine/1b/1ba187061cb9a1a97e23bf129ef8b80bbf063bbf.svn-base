
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

// interface for BlockMemory to asking clobbering queries on particular
// call sites and traces.

#include <imlang/block.h>

NAMESPACE_XGILL_BEGIN

// forward declarations.
class BlockMemory;
struct GuardAssign;

// kinds of clobbering backends. each kind is associated uniquely with
// a particular statically allocated backend.
enum MemoryClobberKind {
  // never clobber anything.
  MCLB_Default = 0,

  // clobber the lvalues indicated by modset information.
  MCLB_Modset = 1,

  // as with MCLB_Modset, but clobbers from indirect calls are not used.
  MCLB_ModsetNoIndirect = 2
};

class MemoryClobber
{
 public:
  // get the backend associated with the specified kind.
  static MemoryClobber* Lookup(MemoryClobberKind kind);

 public:
  MemoryClobber(MemoryClobberKind kind)
    : m_kind(kind)
  {
    Register(this);
  }

  MemoryClobberKind Kind() const { return m_kind; }

  // precompute any lvalues clobbered by the specified edge and add them
  // to the assigned and clobbered list. these lists do not have to be
  // complete; ClobberLval() will be called when checking any lvalue that
  // was not explicitly added to the clobbered list.
  virtual void ComputeClobber(BlockMemory *mcfg, PEdge *edge,
                              Vector<GuardAssign> *assigns,
                              Vector<GuardAssign> *clobbered)
  {}

 private:
  MemoryClobberKind m_kind;

  // register a new backend.
  static void Register(MemoryClobber *clobber);
};

NAMESPACE_XGILL_END
