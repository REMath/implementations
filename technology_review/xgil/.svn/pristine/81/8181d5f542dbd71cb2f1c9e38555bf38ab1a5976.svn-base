
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

// variable representation.

#include <util/hashcons.h>
#include "type.h"

NAMESPACE_XGILL_BEGIN

// forward declarations.
class BlockId;

#define ITERATE_VARIABLE_KINDS(ITER)		\
  ITER(Glob, 1)					\
  ITER(Func, 2)					\
  ITER(Arg, 3)					\
  ITER(Local, 4)				\
  ITER(Temp, 5)					\
  ITER(Return, 6)				\
  ITER(This, 7)

enum VarKind {
  VK_Invalid = 0,
#define ITER(NAME, NUM) VK_ ## NAME = NUM,
  ITERATE_VARIABLE_KINDS(ITER)
#undef ITER
};

class Variable : public HashObject
{
 public:
  static int Compare(const Variable *v0, const Variable *v1);
  static Variable* Copy(const Variable *v);
  static void Write(Buffer *buf, const Variable *v);
  static Variable* Read(Buffer *buf);

  static Variable* Make(BlockId *id, VarKind kind,
                        String *name, size_t index, String *source_name) {
    Variable xv(id, kind, name, index, source_name);
    return g_table.Lookup(xv);
  }

 public:
  // gets the block this variable was declared in, or NULL if there
  // is no block (global variables, call site arguments, etc.)
  BlockId* GetId() const { return m_id; }

  // get the kind of this variable.
  VarKind Kind() const { return m_kind; }

  // get the name of this variable, NULL if it has none. global, function,
  // local, and temp variables always have names, arguments sometimes do.
  // no two args/locals/temps for the same function will have the same name,
  // and no two globs/funcs will have the same name.
  String* GetName(bool required = true) const {
    if (required)
      Assert(m_name);
    return m_name;
  }

  // get the index of this variable. requires this is an argument variable.
  size_t GetIndex() const {
    Assert(m_kind == VK_Arg);
    return m_index;
  }

  // get the source name which will be used to print this variable,
  // if available.
  String* GetSourceName() const {
    return m_source_name;
  }

  // is this a global or function variable?
  bool IsGlobal() const {
    return m_kind == VK_Glob || m_kind == VK_Func;
  }

  // get the declared type of this variable, if known. this method uses the
  // databases produced after loop splitting so must not be called before
  // loop splitting is complete.
  Type* GetType() const;

  // returns whether this variable is semantically equivalent to var.
  // this is different from plain equality, as different variable structures
  // may have differences that do not affect the program location referred to,
  // such as whether arguments have names available or an associated block id.
  bool Matches(Variable *var) const;

  // set the type of this variable. if override is set then any previously
  // set type will be overridden without warning.
  void SetType(Type *type, bool override = false);

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;

 private:
  BlockId *m_id;
  VarKind m_kind;
  String *m_name;
  size_t m_index;
  String *m_source_name;

  // type of this variable, if known. this is not part of the identifier for
  // the variable, just the place we hang the type once we determine it.
  Type *m_type;

  Variable(BlockId *id, VarKind kind,
           String *name, size_t index, String *source_name);
  static HashCons<Variable> g_table;
};

NAMESPACE_XGILL_END
