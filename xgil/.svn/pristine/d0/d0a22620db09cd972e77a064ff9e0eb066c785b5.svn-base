
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

#include <util/hashcons.h>
#include "trace.h"
#include "block.h"

NAMESPACE_XGILL_BEGIN

enum TraceKind {
  TK_Invalid = 0,
  TK_Func = 1,
  TK_Glob = 2,
  TK_Comp = 3
};

class Trace : public HashObject
{
 public:
  static int Compare(const Trace *t0, const Trace *t1);
  static Trace* Copy(const Trace *t);
  static void Write(Buffer *buf, const Trace *t);
  static Trace* Read(Buffer *buf);

  static Trace* MakeFunc(Exp *value, Variable *function,
                         const Vector<BlockPPoint> &context);
  static Trace* MakeFunc(Exp *value, Variable *function);
  static Trace* MakeGlob(Exp *value);
  static Trace* MakeComp(Exp *value, String *csu_name);

  // replace the expression in a trace with new_value. gets a reference on
  // the result and consumes one on new_value (but not trace).
  static Trace* ReplaceExp(Trace *trace, Exp *new_value);

  // sanitizes an expression appropriately and get a reference on the most
  // specific trace for it. consumes a reference on value, and gets
  // a reference on the result. returns NULL if the trace has no sanitized
  // representation (non-lvalue expressions, constant strings, etc.)
  static Trace* MakeFromExp(BlockId *id, Exp *value);

  // standalone sanitization step for expressions when converting to traces.
  // the result is NULL if value has no sanitized representation.
  static Exp* SanitizeExp(Exp *value);

 public:
  // get the kind of this trace.
  TraceKind Kind() const { return m_kind; }

  // get the expression associated with this trace.
  Exp* GetValue() const { return m_value; }

  // for TK_Func, get the associated function.
  Variable* GetFunction() const {
    Assert(m_kind == TK_Func);
    return m_func;
  }

  // for TK_Func, get any available calling context.
  size_t GetContextCount() const {
    Assert(m_kind == TK_Func);
    return m_context_count;
  }
  BlockPPoint GetContext(size_t ind) const {
    Assert(ind < GetContextCount());
    return m_context[ind];
  }

  // for TK_Comp, get the associated CSU's name.
  String* GetCSUName() const {
    Assert(m_kind == TK_Comp);
    return m_csu;
  }

  // get all traces which could match this trace and store them in matches.
  // gets a reference on each trace added to matches. the matches will be
  // listed from least to most specific; this trace will be the last entry.
  void GetMatches(Vector<Trace*> *matches);

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  TraceKind m_kind;
  Exp *m_value;

  Variable *m_func;
  String *m_csu;

  BlockPPoint *m_context;
  size_t m_context_count;

  Trace(TraceKind kind, Exp *value, Variable *func, String *csu,
        const Vector<BlockPPoint> &context);
  static HashCons<Trace> g_table;
};

// fill in traces with the set of traces which may affect the value of bit
// when updated. for handling type and global invariants.
void GetUpdateTraces(Bit *bit, Vector<Trace*> *traces);

NAMESPACE_XGILL_END
