
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

// actions performed during transaction execution

#include "transaction.h"

NAMESPACE_XGILL_BEGIN

enum TActionKind {
  TA_Invalid = 0,
  TA_Assign = 1,
  TA_Call = 2,
  TA_Sequence = 3,
  TA_Test = 4,
  TA_Iterate = 5
};

class TAction
{
 public:
  static void Write(Buffer *buf, const TAction *a);
  static TAction* Read(Buffer *buf, Transaction *t);

 public:
  TAction(Transaction *t, TActionKind kind)
    : m_kind(kind), m_transaction(t)
  {
    Assert(m_transaction);
    m_transaction->AddAction(this);
  }

  // get the kind of this action
  TActionKind Kind() const { return m_kind; }

  // make sure the destructor gets called on any inherited subclass
  virtual ~TAction() {}

  // print this action to the specified stream, with a count of padding chars.
  virtual void Print(OutStream &out, size_t padding = 0) const = 0;

  // execute this action in the context of a given transaction.
  // returns true on success, false and prints an error otherwise.
  virtual bool Execute() const = 0;

 protected:
  TActionKind m_kind;
  Transaction *m_transaction;
};

// TAction instance classes

class TActionAssign : public TAction
{
 public:
  // create an assign action for the specified operand.
  TActionAssign(Transaction *t, TOperand *value, size_t var);

  size_t GetVar() const { return m_var; }
  TOperand* GetValue() const { return m_value; }

  // inherited methods
  void Print(OutStream &out, size_t padding = 0) const;
  bool Execute() const;

 private:
  // variable being assigned to.
  size_t m_var;

  // operand being assigned to var.
  TOperand *m_value;
};

class TActionCall : public TAction
{
 public:
  // create a call action with the given result (0 for no result)
  // and name. the name must point into a buffer either owned by the
  // transaction or which will outlive the transaction.
  TActionCall(Transaction *t, size_t result_var, const char *name);

  // push an argument onto the end of this call's arguments
  void PushArgument(TOperand *arg);

  size_t GetResultName() const { return m_result_var; }
  const char* GetFunction() const { return m_name; }

  size_t GetArgumentCount() const { return m_arguments.Size(); }
  TOperand* GetArgument(size_t ind) const { return m_arguments[ind]; }

  // inherited methods
  void Print(OutStream &out, size_t padding = 0) const;
  bool Execute() const;

 private:
  size_t m_result_var;
  const char *m_name;
  Vector<TOperand*> m_arguments;
};

class TActionSequence : public TAction
{
 public:
  // create an empty sequence of actions.
  TActionSequence(Transaction *t);

  // push an action onto the end of this sequence.
  void PushAction(TAction *a);

  size_t GetCount() const { return m_body.Size(); }
  TAction* GetAction(size_t ind) const { return m_body[ind]; }

  // inherited methods
  void Print(OutStream &out, size_t padding = 0) const;
  bool Execute() const;

 private:
  Vector<TAction*> m_body;
};

class TActionTest : public TAction
{
 public:
  // create a conditional test on the specified operand,
  // with an empty body
  TActionTest(Transaction *t, TOperand *test, bool run_value);

  // push an action onto the end of this test's conditional body
  void PushAction(TAction *a);

  TOperand* GetTest() const { return m_test; }
  bool IsRunTrue() const { return m_run_value; }

  size_t GetCount() const { return m_body.Size(); }
  TAction* GetAction(size_t ind) const { return m_body[ind]; }

  // inherited methods
  void Print(OutStream &out, size_t padding = 0) const;
  bool Execute() const;

 private:
  TOperand *m_test;
  bool m_run_value;

  Vector<TAction*> m_body;
};

class TActionIterate : public TAction
{
 public:
  // create an iterate action binding a variable to each element
  // of a list in turn and executing an (initially empty) body.
  TActionIterate(Transaction *t, size_t bind_var, TOperand *list);

  // push an action onto the end of this iterator's body
  void PushAction(TAction *a);

  size_t GetBindName() const { return m_bind_var; }
  TOperand* GetList() const { return m_list; }

  size_t GetCount() const { return m_body.Size(); }
  TAction* GetAction(size_t ind) const { return m_body[ind]; }

  // inherited methods
  void Print(OutStream &out, size_t padding = 0) const;
  bool Execute() const;

 private:
  size_t m_bind_var;
  TOperand *m_list;

  Vector<TAction*> m_body;
};

NAMESPACE_XGILL_END
