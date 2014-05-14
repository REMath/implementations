
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

// interface for the backends which execute transaction functions.

#include "transaction.h"
#include "operand.h"
#include "action.h"

NAMESPACE_XGILL_BEGIN

class TransactionBackend;

// interface for a function which can run during a transaction.
// functions return true on success, false and print an error otherwise.
typedef bool (*TFunction)(Transaction *t, const Vector<TOperand*> &arguments,
                          TOperand **result);

// function for starting up or finishing a backend.
typedef void (*TStartFunction)();
typedef void (*TFinishFunction)();

// the transaction backend defines the various functions which
// can be invoked by a transaction.
class TransactionBackend
{
 public:
  // setup all builtin backends for calling functions. this must only
  // be called once.
  static void StartBackend();

  // finish the backends, persisting data to disk if necessary. this must
  // only be called once.
  static void FinishBackend();

  // whether the backends have finished, or are in the process of finishing.
  static bool HasFinishedBackends();

  // run a function in some backend on the specified arguments,
  // returning a result in *result if there is one.
  // return true on success, false and print an error otherwise.
  static bool RunFunction(Transaction *t, const char *name,
                          const Vector<TOperand*> &arguments,
                          TOperand **result);

  // register a function which can be called for this backend.
  // registration should be performed by the start method, and the name
  // should be unique across all backends.
  static void RegisterFunction(const char *name, TFunction function);

 public:
  TransactionBackend(TStartFunction start, TFinishFunction finish)
    : m_start(start), m_finish(finish)
  {}

 private:
  // start and finish functions for this backend. finish may be NULL.
  TStartFunction m_start;
  TFinishFunction m_finish;
};

/////////////////////////////////////////////////////////////////////
// backend macros
/////////////////////////////////////////////////////////////////////

// namespace to put backend implementation functions and data in.

#define BACKEND_IMPL        Backend_IMPL
#define BACKEND_IMPL_BEGIN  namespace Backend_IMPL {
#define BACKEND_IMPL_END    }

// register a function NAME whose implementation is at BACKEND_IMPL::NAME.
#define BACKEND_REGISTER(NAME)                                          \
  TransactionBackend::RegisterFunction(#NAME, Backend_IMPL::NAME);

// make a call to function NAME, storing the result (if any) in RESULT.
#define BACKEND_CALL(NAME, RESULT)                                      \
  TActionCall *call = new TActionCall(t, RESULT, #NAME)

// helpers for writing backend implementation functions.

// macro for bailing out of an implementation function.
#define BACKEND_FAIL(VALUE)                                             \
  do {                                                                  \
    logout << "Backend: Failed at " << __FILE__ << ":" << __LINE__;     \
    TOperand *op = (VALUE);                                             \
    if (op) {                                                           \
      logout << ": ";                                                   \
      op->Print(logout);                                                \
    }                                                                   \
    logout << endl;                                                     \
    return false;                                                       \
  } while (0)

// check that the number of arguments is exactly NUM.
#define BACKEND_ARG_COUNT(NUM)                                  \
  if (arguments.Size() != NUM) BACKEND_FAIL(NULL);

// get a NULL-terminated string from argument POS and store it in NAME/LEN.
// LEN includes the NULL-terminator, i.e. it is strlen(NAME) + 1.
#define BACKEND_ARG_STRING(POS, NAME, LEN)                              \
  if (arguments[POS]->Kind() != TO_String)                              \
    BACKEND_FAIL(arguments[POS]);                                       \
  const uint8_t *NAME = arguments[POS]->AsString()->GetData();          \
  size_t LEN = arguments[POS]->AsString()->GetDataLength();             \
  if (!ValidString(NAME, LEN))                                          \
    BACKEND_FAIL(arguments[POS]);

// get an unformatted string from argument POS and store in DATA/LEN.
#define BACKEND_ARG_DATA(POS, DATA, LEN)                                \
  if (arguments[POS]->Kind() != TO_String)                              \
    BACKEND_FAIL(arguments[POS]);                                       \
  const uint8_t *DATA = arguments[POS]->AsString()->GetData();          \
  size_t LEN = arguments[POS]->AsString()->GetDataLength();

// get a list from argument POS and store in LIST.
#define BACKEND_ARG_LIST(POS, LIST)                                     \
  if (arguments[POS]->Kind() != TO_List)                                \
    BACKEND_FAIL(arguments[POS]);                                       \
  TOperandList *LIST = arguments[POS]->AsList();

// get a boolean from argument POS and store it in VALUE.
#define BACKEND_ARG_BOOLEAN(POS, VALUE)                                 \
  if (arguments[POS]->Kind() != TO_Boolean)                             \
    BACKEND_FAIL(arguments[POS]);                                       \
  bool VALUE = arguments[POS]->AsBoolean()->IsTrue();

// get an integer from argument POS and store it in VALUE.
#define BACKEND_ARG_INTEGER(POS, VALUE)                                 \
  if (arguments[POS]->Kind() != TO_Integer)                             \
    BACKEND_FAIL(arguments[POS]);                                       \
  uint32_t VALUE = arguments[POS]->AsInteger()->GetValue();

// helpers for constructing transactions.

#define TRANSACTION_MAKE_VAR(NAME)                              \
  size_t NAME ## _var = t->MakeVariable(false);                 \
  TOperand *NAME = new TOperandVariable(t, NAME ## _var);

NAMESPACE_XGILL_END
