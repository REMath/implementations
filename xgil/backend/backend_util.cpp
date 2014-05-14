
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

#include "backend_util.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// backend implementations
/////////////////////////////////////////////////////////////////////

BACKEND_IMPL_BEGIN

TAction* ValueLess(Transaction *t,
                   TOperand *v0, TOperand *v1,
                   size_t var_result);

TAction* ValueLessEqual(Transaction *t,
                        TOperand *v0, TOperand *v1,
                        size_t var_result);

TAction* ValueEqual(Transaction *t,
                    TOperand *v0, TOperand *v1,
                    size_t var_result);

bool ValueLess(Transaction *t,
               const Vector<TOperand*> &arguments,
               TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_INTEGER(0, v0);
  BACKEND_ARG_INTEGER(1, v1);

  *result = new TOperandBoolean(t, v0 < v1);
  return true;
}

bool ValueLessEqual(Transaction *t,
                    const Vector<TOperand*> &arguments,
                    TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_INTEGER(0, v0);
  BACKEND_ARG_INTEGER(1, v1);

  *result = new TOperandBoolean(t, v0 <= v1);
  return true;
}

bool ValueEqual(Transaction *t,
                const Vector<TOperand*> &arguments,
                TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_INTEGER(0, v0);
  BACKEND_ARG_INTEGER(1, v1);

  *result = new TOperandBoolean(t, v0 == v1);
  return true;
}

bool StringIsEmpty(Transaction *t,
                   const Vector<TOperand*> &arguments,
                   TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, str, str_length);

  *result = new TOperandBoolean(t, str_length == 1);
  return true;
}

bool ListCreate(Transaction *t,
                const Vector<TOperand*> &arguments,
                TOperand **result)
{
  TOperandList *res = new TOperandList(t);

  for (size_t aind = 0; aind < arguments.Size(); aind++)
    res->PushOperand(arguments[aind]);

  *result = res;
  return true;
}

bool ListPush(Transaction *t,
              const Vector<TOperand*> &arguments,
              TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_LIST(0, list);

  // make a copy of the argument list, do not modify it directly.
  TOperandList *res = new TOperandList(t);
  for (size_t lind = 0; lind < list->GetCount(); lind++)
    res->PushOperand(list->GetOperand(lind));
  res->PushOperand(arguments[1]);

  *result = res;
  return true;
}

// information about a counter.
struct CounterInfo {
  String *name;
  size_t count;
};

// list of all counters.
Vector<CounterInfo> counters;

bool CounterInc(Transaction *t,
                const Vector<TOperand*> &arguments,
                TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, name, name_length);

  String *key = String::Make((const char*) name);

  for (size_t ind = 0; ind < counters.Size(); ind++) {
    if (key == counters[ind].name) {
      counters[ind].count++;
      return true;
    }
  }

  CounterInfo info;
  info.name = key;
  info.count = 1;
  counters.PushBack(info);

  return true;
}

bool CounterDec(Transaction *t,
                const Vector<TOperand*> &arguments,
                TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, name, name_length);

  String *key = String::Make((const char*) name);

  for (size_t ind = 0; ind < counters.Size(); ind++) {
    if (key == counters[ind].name) {
      if (counters[ind].count == 0) {
        logout << "ERROR: Decrement on empty counter: " << key << endl;
        return false;
      }

      counters[ind].count--;
      return true;
    }
  }

  logout << "ERROR: Decrement on missing counter: " << key << endl;
  return true;
}

bool CounterValue(Transaction *t,
                  const Vector<TOperand*> &arguments,
                  TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, name, name_length);

  String *key = String::Make((const char*) name);

  for (size_t ind = 0; ind < counters.Size(); ind++) {
    if (key == counters[ind].name) {
      *result = new TOperandInteger(t, counters[ind].count);
      return true;
    }
  }

  *result = new TOperandInteger(t, 0);
  return true;
}

bool FileRead(Transaction *t,
              const Vector<TOperand*> &arguments,
              TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, name, name_length);

  Buffer *buf = new Buffer();
  t->AddBuffer(buf);

  ifstream in((const char*) name);
  ReadInStream(in, buf);

  *result = new TOperandString(t, (const char*) buf->base);
  return true;
}

BACKEND_IMPL_END

/////////////////////////////////////////////////////////////////////
// backend
/////////////////////////////////////////////////////////////////////

static void start_Util()
{
  BACKEND_REGISTER(ValueLess);
  BACKEND_REGISTER(ValueLessEqual);
  BACKEND_REGISTER(ValueEqual);
  BACKEND_REGISTER(StringIsEmpty);
  BACKEND_REGISTER(ListCreate);
  BACKEND_REGISTER(ListPush);
  BACKEND_REGISTER(CounterInc);
  BACKEND_REGISTER(CounterDec);
  BACKEND_REGISTER(CounterValue);
  BACKEND_REGISTER(FileRead);
}

static void finish_Util()
{}

TransactionBackend backend_Util(start_Util, finish_Util);

/////////////////////////////////////////////////////////////////////
// backend wrappers
/////////////////////////////////////////////////////////////////////

NAMESPACE_BEGIN(Backend)

TAction* ValueLess(Transaction *t,
                   TOperand *v0, TOperand *v1,
                   size_t var_result)
{
  BACKEND_CALL(ValueLess, var_result);
  call->PushArgument(v0);
  call->PushArgument(v1);
  return call;
}

TAction* ValueLessEqual(Transaction *t,
                        TOperand *v0, TOperand *v1,
                        size_t var_result)
{
  BACKEND_CALL(ValueLessEqual, var_result);
  call->PushArgument(v0);
  call->PushArgument(v1);
  return call;
}

TAction* ValueEqual(Transaction *t,
                    TOperand *v0, TOperand *v1,
                    size_t var_result)
{
  BACKEND_CALL(ValueEqual, var_result);
  call->PushArgument(v0);
  call->PushArgument(v1);
  return call;
}

TAction* StringIsEmpty(Transaction *t, TOperand *str,
                       size_t var_result)
{
  BACKEND_CALL(StringIsEmpty, var_result);
  call->PushArgument(str);
  return call;
}

TAction* ListEmpty(Transaction *t, size_t var_result)
{
  BACKEND_CALL(ListCreate, var_result);
  return call;
}

TAction* ListCreate(Transaction *t, const Vector<TOperand*> &args,
                    size_t var_result)
{
  BACKEND_CALL(ListCreate, var_result);
  for (size_t aind = 0; aind < args.Size(); aind++)
    call->PushArgument(args[aind]);
  return call;
}

TAction* ListPush(Transaction *t, TOperand *list, TOperand *arg,
                  size_t var_result)
{
  BACKEND_CALL(ListPush, var_result);
  call->PushArgument(list);
  call->PushArgument(arg);
  return call;
}

TAction* CounterInc(Transaction *t, const char *name)
{
  BACKEND_CALL(CounterInc, 0);
  call->PushArgument(new TOperandString(t, name));
  return call;
}

TAction* CounterDec(Transaction *t, const char *name)
{
  BACKEND_CALL(CounterDec, 0);
  call->PushArgument(new TOperandString(t, name));
  return call;
}

TAction* CounterValue(Transaction *t, const char *name, size_t var_result)
{
  BACKEND_CALL(CounterValue, var_result);
  call->PushArgument(new TOperandString(t, name));
  return call;
}

TAction* FileRead(Transaction *t, const char *name, size_t var_result)
{
  BACKEND_CALL(FileRead, var_result);
  call->PushArgument(new TOperandString(t, name));
  return call;
}

NAMESPACE_END(Backend)

NAMESPACE_XGILL_END
