
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

#include "variable.h"
#include "block.h"
#include "storage.h"

NAMESPACE_XGILL_BEGIN

// define to print the fully decorated names of program variables.
// #define VARIABLE_PRINT_DECORATED

/////////////////////////////////////////////////////////////////////
// Variable static
/////////////////////////////////////////////////////////////////////

HashCons<Variable> Variable::g_table;

int Variable::Compare(const Variable *v0, const Variable *v1)
{
  TryCompareObjects(v0->GetId(), v1->GetId(), BlockId);
  TryCompareValues(v0->Kind(), v1->Kind());
  TryCompareObjects(v0->GetName(false), v1->GetName(false), String);
  if (v0->Kind() == VK_Arg)
    TryCompareValues(v0->GetIndex(), v1->GetIndex());

  // do not compare source names.
  return 0;
}

Variable* Variable::Copy(const Variable *v)
{
  return new Variable(*v);
}

void Variable::Write(Buffer *buf, const Variable *v)
{
  WriteOpenTag(buf, TAG_Variable);
  if (v->GetId())
    BlockId::Write(buf, v->GetId());
  WriteTagUInt32(buf, TAG_Kind, v->Kind());
  if (v->GetName(false) != NULL)
    String::WriteWithTag(buf, v->GetName(), TAG_Name);
  if (v->GetSourceName() != NULL)
    String::WriteWithTag(buf, v->GetSourceName(), TAG_Name);
  if (v->Kind() == VK_Arg)
    WriteTagUInt32(buf, TAG_Index, v->GetIndex());
  WriteCloseTag(buf, TAG_Variable);
}

Variable* Variable::Read(Buffer *buf)
{
  BlockId *id = NULL;
  uint32_t kind = 0;
  uint32_t index = 0;
  String *name = NULL;
  String *source_name = NULL;

  Try(ReadOpenTag(buf, TAG_Variable));
  while (!ReadCloseTag(buf, TAG_Variable)) {
    switch (PeekOpenTag(buf)) {
    case TAG_BlockId: {
      Try(!id);
      id = BlockId::Read(buf);
      break;
    }
    case TAG_Kind: {
      Try(!kind);
      Try(ReadTagUInt32(buf, TAG_Kind, &kind));
      break;
    }
    case TAG_Name: {
      if (name) {
        Try(!source_name);
        source_name = String::ReadWithTag(buf, TAG_Name);
      }
      else {
        name = String::ReadWithTag(buf, TAG_Name);
      }
      break;
    }
    case TAG_Index: {
      Try(kind == VK_Arg);
      Try(ReadTagUInt32(buf, TAG_Index, &index));
      break;
    }
    default:
      Try(false);
    }
  }

  return Make(id, (VarKind)kind, name, index, source_name);
}

/////////////////////////////////////////////////////////////////////
// Variable
/////////////////////////////////////////////////////////////////////

Variable::Variable(BlockId *id, VarKind kind, String *name, size_t index,
                   String *source_name)
  : m_id(id), m_kind(kind),
    m_name(name), m_index(index), m_source_name(source_name),
    m_type(NULL)
{
  if (m_id)
    Assert(m_kind != VK_Func && m_kind != VK_Glob);

  if (m_kind == VK_Glob || kind == VK_Func ||
      kind == VK_Local || kind == VK_Temp)
    Assert(m_name);
  else if (m_kind != VK_Arg)
    Assert(!m_name);

  if (m_name == NULL)
    Assert(!m_source_name);

  if (m_id)
    m_hash = m_id->Hash();
  m_hash = Hash32(m_hash, m_kind);
  m_hash = Hash32(m_hash, m_index);
  if (m_name)
    m_hash = Hash32(m_hash, m_name->Hash());
}

Type* Variable::GetType() const
{
  if (m_type) {
    // we already know the type of the variable, just use that type.
    return m_type;
  }

  // need to look up the type of the variable from the databases.
  // since the CFG fills in the types of any variables it defines,
  // we just need to make sure that CFG gets loaded and our type should
  // be filled in automatically.

  if (m_kind == VK_Glob) {
    // global variable. we have to lookup the type from the static
    // initializer info for this variable.
    InitializerCache.Lookup(m_name);
    InitializerCache.Release(m_name);
  }
  else if (m_kind == VK_Func) {
    // function variable. we have to lookup the type from the CFG for this
    // variable. use BlockCFGCache; this shouldn't be called during
    // loopsplitting (TODO: should make sure of this).

    // lose the const for adding references to this object.
    Variable *me = (Variable*) this;

    BlockId *func_id = BlockId::Make(B_Function, me);
    BlockCFGCache.Lookup(func_id);
    BlockCFGCache.Release(func_id);
  }
  else if (m_id) {
    // other variables should be defined by the CFG containing the variable.
    BlockCFGCache.Lookup(m_id);
    BlockCFGCache.Release(m_id);
  }

  return m_type;
}

bool Variable::Matches(Variable *var) const
{
  if (m_kind != var->Kind())
    return false;

  if (m_kind == VK_Arg)
    return (m_index == var->GetIndex());

  if (m_name)
    return (m_name == var->GetName());

  return true;
}

void Variable::SetType(Type *type, bool override)
{
  Assert(type);
  if (m_type) {
    if (m_type != type && !override)
      logout << "ERROR: Conflicting types for " << this << ": "
             << m_type << " " << type << endl;
  }

  m_type = type;
}

void Variable::Print(OutStream &out) const
{
#ifdef VARIABLE_PRINT_DECORATED

  if (m_id)
    out << "{" << m_id << "}";

  if (m_name && m_kind != VK_Arg) {
    out << m_name->Value();
    return;
  }

#else // VARIABLE_PRINT_DECORATED

  if (m_source_name && m_kind != VK_Local) {
    out << m_source_name->Value();
    return;
  }

  if (m_name) {
    out << m_name->Value();
    return;
  }

#endif // VARIABLE_PRINT_DECORATED

  switch (m_kind) {
  case VK_Glob:
  case VK_Func:
  case VK_Local:
  case VK_Temp:
    // these variables must have names.
    Assert(false);
    break;
  case VK_Arg:
    out << "__arg" << m_index;
    break;
  case VK_Return:
    out << "return";
    break;
  case VK_This:
    out << "this";
    break;
  default:
    Assert(false);
  }
}

void Variable::MarkChildren() const
{
  if (m_id)
    m_id->Mark();
  if (m_name)
    m_name->Mark();
  if (m_source_name)
    m_source_name->Mark();
}

NAMESPACE_XGILL_END
