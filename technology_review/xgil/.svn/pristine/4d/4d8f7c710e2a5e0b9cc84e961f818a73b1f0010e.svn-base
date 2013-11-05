
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

#include "action.h"
#include "backend.h"
#include "serial.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// TAction static
/////////////////////////////////////////////////////////////////////

void TAction::Write(Buffer *buf, const TAction *a)
{
  WriteOpenTag(buf, TAG_TAction);
  WriteTagUInt32(buf, TAG_Kind, a->Kind());

  switch (a->Kind()) {
  case TA_Assign: {
    const TActionAssign *na = (const TActionAssign*)a;
    WriteTagUInt32(buf, TAG_Index, na->GetVar());
    TOperand::Write(buf, na->GetValue());
    break;
  }
  case TA_Call: {
    const TActionCall *na = (const TActionCall*)a;
    WriteTagUInt32(buf, TAG_Index, na->GetResultName());
    WriteTagString(buf, TAG_Name,
                   (const uint8_t*) na->GetFunction(),
                   strlen(na->GetFunction()) + 1);
    for (size_t oind = 0; oind < na->GetArgumentCount(); oind++)
      TOperand::Write(buf, na->GetArgument(oind));
    break;
  }
  case TA_Sequence: {
    const TActionSequence *na = (const TActionSequence*)a;
    for (size_t aind = 0; aind < na->GetCount(); aind++)
      TAction::Write(buf, na->GetAction(aind));
    break;
  }
  case TA_Test: {
    const TActionTest *na = (const TActionTest*)a;
    TOperand::Write(buf, na->GetTest());
    WriteTagEmpty(buf, na->IsRunTrue() ? TAG_True : TAG_False);
    for (size_t aind = 0; aind < na->GetCount(); aind++)
      TAction::Write(buf, na->GetAction(aind));
    break;
  }
  case TA_Iterate: {
    const TActionIterate *na = (const TActionIterate*)a;
    WriteTagUInt32(buf, TAG_Index, na->GetBindName());
    TOperand::Write(buf, na->GetList());
    for (size_t aind = 0; aind < na->GetCount(); aind++)
      TAction::Write(buf, na->GetAction(aind));
    break;
  }
  default:
    Assert(false);
  }

  WriteCloseTag(buf, TAG_TAction);
}

TAction* TAction::Read(Buffer *buf, Transaction *t)
{
  uint32_t kind = 0;
  uint32_t index = 0;
  bool is_true = false;
  bool is_false = false;
  const uint8_t *name_str = NULL;
  Vector<TOperand*> operands;
  Vector<TAction*> actions;

  Try(ReadOpenTag(buf, TAG_TAction));
  while (!ReadCloseTag(buf, TAG_TAction)) {
    switch (PeekOpenTag(buf)) {
    case TAG_Kind: {
      Try(!kind);
      Try(ReadTagUInt32(buf, TAG_Kind, &kind));
      break;
    }
    case TAG_Index: {
      Try(!index);
      Try(kind == TA_Assign || kind == TA_Call || kind == TA_Iterate);
      Try(ReadTagUInt32(buf, TAG_Index, &index));
      break;
    }
    case TAG_True: {
      Try(!is_true && !is_false);
      Try(kind == TA_Test);
      Try(ReadTagEmpty(buf, TAG_True));
      is_true = true;
      break;
    }
    case TAG_False: {
      Try(!is_true && !is_false);
      Try(kind == TA_Test);
      Try(ReadTagEmpty(buf, TAG_False));
      is_false = true;
      break;
    }
    case TAG_Name: {
      Try(!name_str);
      Try(kind == TA_Call);
      size_t str_len = 0;
      Try(ReadTagString(buf, TAG_Name, &name_str, &str_len));
      Try(str_len != 0 && name_str[str_len-1] == '\0');
      break;
    }
    case TAG_TOperand: {
      Try(kind == TA_Assign || kind == TA_Test ||
          kind == TA_Iterate || kind == TA_Call);
      TOperand *op;
      Try(op = TOperand::Read(buf, t));
      operands.PushBack(op);
      break;
    }
    case TAG_TAction: {
      Try(kind == TA_Sequence || kind == TA_Test || kind == TA_Iterate);
      TAction *a;
      Try(a = TAction::Read(buf, t));
      actions.PushBack(a);
      break;
    }
    default:
      Try(false);
    }
  }

  switch ((TActionKind)kind) {
  case TA_Assign:
    Try(index);
    Try(operands.Size() == 1);
    return new TActionAssign(t, operands[0], index);
  case TA_Call: {
    Try(name_str);
    TActionCall *call = new TActionCall(t, index, (const char*) name_str);
    for (size_t oind = 0; oind < operands.Size(); oind++)
      call->PushArgument(operands[oind]);
    return call;
  }
  case TA_Sequence: {
    TActionSequence *sequence = new TActionSequence(t);
    for (size_t aind = 0; aind < actions.Size(); aind++)
      sequence->PushAction(actions[aind]);
    return sequence;
  }
  case TA_Test: {
    Try(operands.Size() == 1);
    Try(is_true || is_false);
    TActionTest *test = new TActionTest(t, operands[0], is_true);
    for (size_t aind = 0; aind < actions.Size(); aind++)
      test->PushAction(actions[aind]);
    return test;
  }
  case TA_Iterate: {
    Try(index);
    Try(operands.Size() == 1);
    TActionIterate *iterate = new TActionIterate(t, index, operands[0]);
    for (size_t aind = 0; aind < actions.Size(); aind++)
      iterate->PushAction(actions[aind]);
    return iterate;
  }
  default:
    Try(false);
    return NULL;
  }
}

/////////////////////////////////////////////////////////////////////
// TActionAssign
/////////////////////////////////////////////////////////////////////

TActionAssign::TActionAssign(Transaction *t, TOperand *value, size_t var)
  : TAction(t, TA_Assign), m_var(var), m_value(value)
{
  Assert(m_var != 0);
  Assert(m_value);
}

void TActionAssign::Print(OutStream &out, size_t padding) const
{
  PrintPadding(out, padding);
  out << "$" << m_var << " := ";
  m_value->Print(out);
  out << endl;
}

bool TActionAssign::Execute() const
{
  TOperand *value = m_value->Instantiate();
  if (value == NULL)
    return false;
  m_transaction->Assign(m_var, value);
  return true;
}

/////////////////////////////////////////////////////////////////////
// TActionCall
/////////////////////////////////////////////////////////////////////

TActionCall::TActionCall(Transaction *t, size_t result_var, const char *name)
  : TAction(t, TA_Call), m_result_var(result_var), m_name(name)
{
  Assert(m_name);
}

void TActionCall::PushArgument(TOperand *arg)
{
  Assert(arg);
  m_arguments.PushBack(arg);
}

void TActionCall::Print(OutStream &out, size_t padding) const
{
  PrintPadding(out, padding);
  if (m_result_var != 0)
    out << "$" << (long)m_result_var << " := ";
  out << m_name << "(";
  for (size_t ind = 0; ind < m_arguments.Size(); ind++) {
    if (ind != 0)
      out << ", ";
    m_arguments[ind]->Print(out);
  }
  out << ")" << endl;
}

bool TActionCall::Execute() const
{
  Vector<TOperand*> actuals;
  for (size_t aind = 0; aind < m_arguments.Size(); aind++) {
    TOperand *arg = m_arguments[aind]->Instantiate();
    if (arg == NULL)
      return false;
    actuals.PushBack(arg);
  }

  TOperand *result = NULL;
  bool res = TransactionBackend::RunFunction(m_transaction, m_name,
                                             actuals, &result);
  if (!res) {
    logout << "ERROR: Failure executing function " << m_name << endl;
    return false;
  }

  if (m_result_var != 0) {
    if (result == NULL) {
      logout << "ERROR: Function " << m_name
           << " did not return a value." << endl;
      return false;
    }
    else {
      m_transaction->Assign(m_result_var, result);
      return true;
    }
  }
  else {
    return true;
  }
}

/////////////////////////////////////////////////////////////////////
// TActionSequence
/////////////////////////////////////////////////////////////////////

TActionSequence::TActionSequence(Transaction *t)
  : TAction(t, TA_Sequence)
{}

void TActionSequence::PushAction(TAction *a)
{
  if (a != NULL)
    m_body.PushBack(a);
}

void TActionSequence::Print(OutStream &out, size_t padding) const
{
  for (size_t aind = 0; aind < m_body.Size(); aind++)
    m_body[aind]->Print(out, padding);
}

bool TActionSequence::Execute() const
{
  for (size_t aind = 0; aind < m_body.Size(); aind++) {
    bool res = m_body[aind]->Execute();
    if (!res)
      return false;
  }
  return true;
}

/////////////////////////////////////////////////////////////////////
// TActionTest
/////////////////////////////////////////////////////////////////////

TActionTest::TActionTest(Transaction *t, TOperand *test, bool run_value)
  : TAction(t, TA_Test), m_test(test), m_run_value(run_value)
{
  Assert(m_test);
}

void TActionTest::PushAction(TAction *a)
{
  if (a != NULL)
    m_body.PushBack(a);
}

void TActionTest::Print(OutStream &out, size_t padding) const
{
  PrintPadding(out, padding);
  out << "if ";
  if (!m_run_value)
    out << "!";
  m_test->Print(out);
  out << endl;

  for (size_t aind = 0; aind < m_body.Size(); aind++)
    m_body[aind]->Print(out, padding + 2);
}

bool TActionTest::Execute() const
{
  TOperand *value = m_test->Instantiate();
  if (value == NULL)
    return false;

  if (value->Kind() != TO_Boolean) {
    logout << "ERROR: Test action must be on a boolean value." << endl;
    return false;
  }

  bool bool_value = ((TOperandBoolean*)value)->IsTrue();
  if (bool_value == m_run_value) {

    // run the body
    for (size_t aind = 0; aind < m_body.Size(); aind++) {
      bool res = m_body[aind]->Execute();
      if (!res)
        return false;
    }
    return true;
  }
  else {
    return true;
  }
}

/////////////////////////////////////////////////////////////////////
// TActionIterate
/////////////////////////////////////////////////////////////////////

TActionIterate::TActionIterate(Transaction *t, size_t bind_var,
                               TOperand *list)
  : TAction(t, TA_Iterate), m_bind_var(bind_var), m_list(list)
{
  Assert(m_bind_var != 0);
  Assert(m_list);
}

void TActionIterate::PushAction(TAction *a)
{
  if (a != NULL)
    m_body.PushBack(a);
}

void TActionIterate::Print(OutStream &out, size_t padding) const
{
  PrintPadding(out, padding);
  out << "foreach $" << (long)m_bind_var << " in ";
  m_list->Print(out);
  out << endl;

  for (size_t aind = 0; aind < m_body.Size(); aind++)
    m_body[aind]->Print(out, padding + 2);
}

bool TActionIterate::Execute() const
{
  TOperand *value = m_list->Instantiate();
  if (value == NULL)
    return false;

  if (value->Kind() != TO_List) {
    logout << "ERROR: Iterate action must be on a list value." << endl;
    return false;
  }

  TOperandList *list_value = (TOperandList*)value;
  for (size_t lind = 0; lind < list_value->GetCount(); lind++) {
    TOperand *val = list_value->GetOperand(lind);
    m_transaction->Assign(m_bind_var, val);

    // run the body
    for (size_t aind = 0; aind < m_body.Size(); aind++) {
      bool res = m_body[aind]->Execute();
      if (!res)
        return false;
    }
  }

  return true;
}

NAMESPACE_XGILL_END
