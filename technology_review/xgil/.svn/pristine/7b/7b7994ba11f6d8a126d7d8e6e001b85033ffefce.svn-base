
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

#include "trace.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// LocTrace static
/////////////////////////////////////////////////////////////////////

HashCons<Trace> Trace::g_table;

int Trace::Compare(const Trace *trace0, const Trace *trace1)
{
  TryCompareValues(trace0->m_kind, trace1->m_kind);
  TryCompareObjects(trace0->m_value, trace1->m_value, Exp);
  TryCompareObjects(trace0->m_func, trace1->m_func, Variable);
  TryCompareObjects(trace0->m_csu, trace1->m_csu, String);

  TryCompareValues(trace0->m_context_count, trace1->m_context_count);
  for (size_t cind = 0; cind < trace0->m_context_count; cind++) {
    const BlockPPoint &bp0 = trace0->m_context[cind];
    const BlockPPoint &bp1 = trace1->m_context[cind];
    TryCompareObjects(bp0.id, bp1.id, BlockId);
    TryCompareValues(bp0.point, bp1.point);
  }

  return 0;
}

Trace* Trace::Copy(const Trace *trace)
{
  return new Trace(*trace);
}

void Trace::Write(Buffer *buf, const Trace *trace)
{
  WriteOpenTag(buf, TAG_Trace);
  WriteTagUInt32(buf, TAG_Kind, trace->Kind());
  Exp::Write(buf, trace->GetValue());

  switch (trace->Kind()) {
  case TK_Func:
    Variable::Write(buf, trace->GetFunction());
    for (size_t cind = 0; cind < trace->GetContextCount(); cind++)
      BlockPPoint::Write(buf, trace->GetContext(cind));
    break;
  case TK_Glob:
    break;
  case TK_Comp:
    String::WriteWithTag(buf, trace->GetCSUName(), TAG_Name);
    break;
  default:
    Assert(false);
  }

  WriteCloseTag(buf, TAG_Trace);
}

Trace* Trace::Read(Buffer *buf)
{
  uint32_t kind = 0;
  Exp *exp = NULL;
  Variable *func = NULL;
  String *csu = NULL;
  Vector<BlockPPoint> context;

  Try(ReadOpenTag(buf, TAG_Trace));
  while (!ReadCloseTag(buf, TAG_Trace)) {
    switch (PeekOpenTag(buf)) {
    case TAG_Kind: {
      Try(!kind);
      Try(ReadTagUInt32(buf, TAG_Kind, &kind));
      break;
    }
    case TAG_Exp: {
      Try(!exp);
      exp = Exp::Read(buf);
      break;
    }
    case TAG_Variable: {
      Try(!func);
      func = Variable::Read(buf);
      break;
    }
    case TAG_Name: {
      Try(!csu);
      csu = String::ReadWithTag(buf, TAG_Name);
      break;
    }
    case TAG_BlockPPoint: {
      BlockPPoint bp = BlockPPoint::Read(buf);
      Try(bp.id);
      context.PushBack(bp);
      break;
    }
    default:
      Try(false);
    }
  }

  Try(kind);
  Trace xtrace((TraceKind) kind, exp, func, csu, context);
  return g_table.Lookup(xtrace);
}

Trace* Trace::MakeFunc(Exp *value, Variable *function,
                       const Vector<BlockPPoint> &context)
{
  Variable *root = value->Root();
  Assert(root && !root->IsGlobal());

  Trace xtrace(TK_Func, value, function, NULL, context);
  return g_table.Lookup(xtrace);
}

Trace* Trace::MakeFunc(Exp *value, Variable *function)
{
  Variable *root = value->Root();
  Assert(root && !root->IsGlobal());

  Vector<BlockPPoint> context;
  Trace xtrace(TK_Func, value, function, NULL, context);
  return g_table.Lookup(xtrace);
}

Trace* Trace::MakeGlob(Exp *value)
{
  Variable *root = value->Root();
  Assert(root && root->IsGlobal());

  Vector<BlockPPoint> context;
  Trace xtrace(TK_Glob, value, NULL, NULL, context);
  return g_table.Lookup(xtrace);
}

Trace* Trace::MakeComp(Exp *value, String *csu_name)
{
  Assert(value->IsRelative());

  Vector<BlockPPoint> context;
  Trace xtrace(TK_Comp, value, NULL, csu_name, context);
  return g_table.Lookup(xtrace);
}

Trace* Trace::ReplaceExp(Trace *trace, Exp *new_value)
{
  Vector<BlockPPoint> context;
  Variable *func = NULL;
  String *csu = NULL;

  switch (trace->Kind()) {
  case TK_Func: {
    func = trace->GetFunction();
    for (size_t ind = 0; ind < trace->GetContextCount(); ind++) {
      BlockPPoint where = trace->GetContext(ind);
      context.PushBack(where);
    }
    break;
  }
  case TK_Comp: {
    csu = trace->GetCSUName();
    break;
  }
  case TK_Glob:
    break;
  default:
    Assert(false);
  }

  Trace xtrace(trace->Kind(), new_value, func, csu, context);
  return g_table.Lookup(xtrace);
}

// sanitize an expression for use in an escape edge or access, if possible.
class SanitizeMapper : public ExpMapper
{
 public:
  SanitizeMapper()
    : ExpMapper(VISK_SubExprs, WIDK_Drop)
  {}

  Exp* Map(Exp *exp, Exp *old)
  {
    if (exp == NULL)
      return NULL;

    // sanitization to do:
    // - normalize ExpVar variables.
    // - remove ExpIndex, use the base expression instead.
    // - convert ExpClobber to ExpDrf.
    // - filter out strings and rvalue expressions.

    switch (exp->Kind()) {

    case EK_Empty:
      // should never see relative expressions here.
      Assert(false);
      return NULL;

    case EK_Var: {
      // sanitized variables have no ID associated, no source name
      // and no name at all for arguments.
      ExpVar *nexp = exp->AsVar();
      Variable *var = nexp->GetVariable();

      VarKind kind = var->Kind();
      String *name = var->GetName(false);
      size_t index = 0;
      if (kind == VK_Arg) {
        name = NULL;
        index = var->GetIndex();
      }

      Variable *new_var = Variable::Make(NULL, kind, name, index, NULL);
      return Exp::MakeVar(new_var);
    }

    case EK_Index: {
      ExpIndex *nexp = exp->AsIndex();
      Exp *target = nexp->GetTarget();
      return target;
    }

    case EK_Clobber: {
      ExpClobber *nexp = exp->AsClobber();
      if (!nexp->GetValueKind()) {
        Exp *target = nexp->GetOverwrite();

        // this is treated as a leaf by the mapper and the target has not
        // been traversed yet. do this now.
        Exp *new_target = target->DoMap(this);

        if (new_target)
          return Exp::MakeDrf(new_target);
      }
      return NULL;
    }

    case EK_Drf:
    case EK_Fld:
    case EK_Rfld:
      return exp;

    default:
      return NULL;
    }
  }
};

Exp* Trace::SanitizeExp(Exp *exp)
{
  SanitizeMapper mapper;
  return exp->DoMap(&mapper);
}

Trace* Trace::MakeFromExp(BlockId *id, Exp *exp)
{
  Exp *new_exp = SanitizeExp(exp);

  if (new_exp == NULL)
    return NULL;

  Variable *var = new_exp->Root();
  Assert(var != NULL);

  if (var->IsGlobal())
    return MakeGlob(new_exp);

  Variable *function = id->BaseVar();

  Vector<BlockPPoint> context;
  return MakeFunc(new_exp, function, context);
}

/////////////////////////////////////////////////////////////////////
// Trace
/////////////////////////////////////////////////////////////////////

Trace::Trace(TraceKind kind, Exp *value, Variable *func, String *csu,
             const Vector<BlockPPoint> &context)
  : m_kind(kind), m_value(value), m_func(func), m_csu(csu),
    m_context(context.Data()), m_context_count(context.Size())
{
  Assert(m_value);
  Assert(!func || !csu);
  Assert(func || csu || m_kind == TK_Glob);

  m_hash = Hash32(m_kind, m_value->Hash());
  if (m_func)
    m_hash = Hash32(m_hash, m_func->Hash());
  if (m_csu)
    m_hash = Hash32(m_hash, m_csu->Hash());
  for (size_t cind = 0; cind < m_context_count; cind++) {
    m_hash = Hash32(m_hash, m_context[cind].id->Hash());
    m_hash = Hash32(m_hash, m_context[cind].point);
  }
}

void Trace::GetMatches(Vector<Trace*> *matches)
{
  Assert(matches->Empty());

  Vector<Exp*> remainders;
  Exp::GetSubExprs(m_value, NULL, &remainders);

  // for every field subexpr of the location, add an TK_Comp for that field.
  // visit the remainders in reverse order so that we see the smallest
  // remainder (and hence least specific TK_Comp) first.
  for (ssize_t rind = remainders.Size() - 1; rind >= 0; rind--) {
    Exp *remainder = remainders[rind];

    if (remainder == m_value) {
      // if the initial exp is also relative then avoid the duplicate add.
      continue;
    }

    Field *field = remainder->BaseField();
    if (field != NULL) {
      String *csu_name = field->GetCSUType()->GetCSUName();

      // make the new trace location and consume the reference
      // on remainder we got from GetSubExprs.
      Trace *rem_trace = MakeComp(remainder, csu_name);
      matches->PushBack(rem_trace);
    }
  }

  // every trace matches itself.
  matches->PushBack(this);
}

void Trace::Print(OutStream &out) const
{
  switch (m_kind) {
  case TK_Func:
    out << "func:" << m_func;
    if (m_context_count > 0) {
      out << "[";
      for (size_t cind = 0; cind < m_context_count; cind++) {
        if (cind != 0)
          out << ",";
        m_context[cind].id->Print(out);
        out << "/" << m_context[cind].point;
      }
      out << "]";
    }
    out << ":";
    break;
  case TK_Glob:
    out << "glob:";
    break;
  case TK_Comp:
    out << "comp:" << m_csu->Value() << ":";
    break;
  default:
    Assert(false);
  }

  out << m_value;
}

void Trace::MarkChildren() const
{
  m_value->Mark();
  if (m_func)
    m_func->Mark();
  if (m_csu)
    m_csu->Mark();

  for (size_t cind = 0; cind < m_context_count; cind++)
    m_context[cind].id->Mark();
}

void Trace::Persist()
{
  if (m_context_count > 0) {
    BlockPPoint *new_context = new BlockPPoint[m_context_count];
    memcpy(new_context, m_context,
           m_context_count * sizeof(BlockPPoint));
    m_context = new_context;
  }
}

void Trace::UnPersist()
{
  if (m_context_count > 0) {
    delete[] m_context;
    m_context = NULL;
  }
}

/////////////////////////////////////////////////////////////////////
// Trace utility
/////////////////////////////////////////////////////////////////////

class UpdateTraceVisitor : public ExpVisitor
{
public:
  Vector<Trace*> *traces;

  UpdateTraceVisitor(Vector<Trace*> *_traces)
    : ExpVisitor(VISK_Lval), traces(_traces)
  {}

  void Visit(Exp *exp)
  {
    Trace *trace = NULL;

    if (ExpFld *nexp = exp->IfFld()) {
      Field *field = nexp->GetField();
      Exp *empty = Exp::MakeEmpty();
      Exp *new_fld = Exp::MakeFld(empty, field);
      String *csu_name = field->GetCSUType()->GetCSUName();
      trace = Trace::MakeComp(new_fld, csu_name);
    }
    else if (Variable *root = exp->Root()) {
      if (root->IsGlobal())
        trace = Trace::MakeFromExp(NULL, exp);
    }

    if (trace) {
      traces->PushBack(trace);
    }
    else {
      // this had better be the 'this' variable, which isn't
      // an lvalue we need to look for updates on.
      Assert(exp->IsVar() && exp->AsVar()->GetVariable()->Kind() == VK_This);
    }
  }
};

void GetUpdateTraces(Bit *bit, Vector<Trace*> *traces)
{
  UpdateTraceVisitor visitor(traces);
  bit->DoVisit(&visitor);
}

NAMESPACE_XGILL_END
