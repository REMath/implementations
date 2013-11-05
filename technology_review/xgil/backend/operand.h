
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

// operands and intermediate values during transaction execution.
// operands do not own any of the data they point to;
// any operands or data specific to the transaction are allocated
// by the transaction itself.

#include "transaction.h"

NAMESPACE_XGILL_BEGIN

enum TOperandKind {
  TO_Invalid = 0,
  TO_Variable = 1,
  TO_List = 2,
  TO_String = 3,
  TO_Boolean = 4,
  TO_Integer = 5
};

class TOperand
{
 public:
  static void Write(Buffer *buf, const TOperand *o);
  static TOperand* Read(Buffer *buf, Transaction *t);

 public:
  TOperand(Transaction *t, TOperandKind kind)
    : m_kind(kind), m_transaction(t)
  {
    Assert(m_transaction);
    m_transaction->AddOperand(this);
  }

  // make sure the destructor gets called on any inherited subclass
  virtual ~TOperand() {}

  TOperandKind Kind() const { return m_kind; }

  // downcasts to the various types of operands.
  TOperandList* AsList() {
    Assert(m_kind == TO_List); return (TOperandList*) this;
  }
  TOperandString* AsString() {
    Assert(m_kind == TO_String); return (TOperandString*) this;
  }
  TOperandBoolean* AsBoolean() {
    Assert(m_kind == TO_Boolean); return (TOperandBoolean*) this;
  }
  TOperandInteger* AsInteger() {
    Assert(m_kind == TO_Integer); return (TOperandInteger*) this;
  }

  // get the value of this operand after replacing variables with their values
  // in the context of the parent transaction. returns NULL if the
  // variable is not currently bound to a value.
  virtual TOperand* Instantiate() { return this; }

  // print this operand to the specified stream
  virtual void Print(OutStream &out) const = 0;

 protected:
  TOperandKind m_kind;
  Transaction *m_transaction;
};

// TOperand instance classes

class TOperandVariable : public TOperand
{
 public:
  TOperandVariable(Transaction *t, size_t name);

  // get the unique name of this variable within the transaction
  size_t GetName() const { return m_name; }

  // inherited methods
  void Print(OutStream &out) const;
  TOperand* Instantiate();

 private:
  size_t m_name;
};

class TOperandList : public TOperand
{
 public:
  TOperandList(Transaction *t);

  // push an operand onto the end of this list
  void PushOperand(TOperand *op);

  // get the operands in this list
  size_t GetCount() const { return m_list.Size(); }
  TOperand* GetOperand(size_t ind) const { return m_list[ind]; }

  // inherited methods
  void Print(OutStream &out) const;

 private:
  Vector<TOperand*> m_list;
};

class TOperandString : public TOperand
{
 public:
  // compresses the in-use portion of buf and returns an operand
  // for the compressed data.
  static TOperandString* Compress(Transaction *t, Buffer *buf);

  // uncompresses the data in op and stores the result in buf.
  static void Uncompress(TOperandString *op, Buffer *buf);

 public:
  // get a string operand containing the specified data.
  // the data must point into a buffer either owned by the transaction
  // or which will outlive the transaction.
  TOperandString(Transaction *t,
                 const uint8_t *data, size_t data_length);

  // get a string operand for a NULL-terminated string.
  // same buffer restrictions as the above constructor.
  TOperandString(Transaction *t,
                 const char *data);

  // get the data for this operand
  const uint8_t* GetData() const { return m_data; }
  size_t GetDataLength() const { return m_data_length; }

  // inherited methods
  void Print(OutStream &out) const;

 private:
  const uint8_t *m_data;
  size_t m_data_length;
};

// test a string operand to see if it is a NULL-terminated C string
inline bool IsCStringOperand(const TOperandString *o)
{
  return o == NULL || ValidString(o->GetData(), o->GetDataLength());
}

class TOperandBoolean : public TOperand
{
 public:
  TOperandBoolean(Transaction *t, bool flag);

  // is this boolean constant true?
  bool IsTrue() const { return m_flag; }

  // inherited methods
  void Print(OutStream &out) const;

 private:
  bool m_flag;
};

class TOperandInteger : public TOperand
{
 public:
  TOperandInteger(Transaction *t, uint32_t value);

  // get the value of this integer constant.
  uint32_t GetValue() const { return m_value; }

  // inherited methods
  void Print(OutStream &out) const;

 private:
  uint32_t m_value;
};

NAMESPACE_XGILL_END
