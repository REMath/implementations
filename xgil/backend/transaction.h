
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

#include <util/buffer.h>
#include <util/primitive.h>

NAMESPACE_XGILL_BEGIN

// transactions overview

// a transaction is some set of read/write operations that can be performed
// on an in-memory hash or on-disk database, and which executes atomically,
// independent of all other actions. submitted transactions will always
// execute; there is no rollback.

// a transaction's behavior is specified with a simple, dynamically typed
// programming language. this language does not currently have a frontend
// syntax or parser; programs constructing transactions construct
// the AST directly.

// primitive values in a transaction (operand.h):
//   strings, boolean constants, integer constants
//   list: a list of values
//   variable: a variable whose value is one of the above. variables can
//     be either temporary vars or return vars. after the transaction
//     executes, the client can query the final value of a return var.

// possible actions in a transaction (action.h):
//   assign: '$x := op'
//   call: '$x := function(op0,op1,...)' with or without a return value
//   sequence: 'a0; a1; ...' sequence of actions
//   test: 'if ([!]op) { a }' test on boolean values
//   iterate: 'foreach $x in op { a }' iterate on a set of values

// most of the expressive power comes in the particular functions that
// can be called. these are left unspecified here and a backend defining
// the possible functions can be plugged in via backend.h

// for operations which can be batched into multiple transactions,
// soft limit on the amount of data that each transaction should contain.
#define TRANSACTION_DATA_LIMIT 512 * 1024

// Transaction class

// forward declarations
class TOperand;
class TOperandList;
class TOperandString;
class TOperandBoolean;
class TOperandInteger;
class TAction;

// all information relating to a transaction, including the action it runs,
// the result it computes, and all memory and buffers allocated for it.
class Transaction
{
 public:
  Transaction();
  ~Transaction();

  // push an action onto the end of this transaction. the transaction itself
  // acts like a TActionSequence.
  void PushAction(TAction *a);

  // get the number of actions which have been added at the top level
  // of this transaction.
  size_t GetActionCount();

  // set this as an initial/final transaction.
  void SetInitial();
  void SetFinal();

  // execute this transaction.
  void Execute();

  // return whether the transaction has been executed.
  bool HasExecuted() const;

  // return whether the transaction's execution succeeded.
  bool HasSuccess() const;

  // return whether this is an initial/final transaction.
  bool IsInitial() const;
  bool IsFinal() const;

  // print out this transaction.
  void Print() const;

 public:
  // information related to serialization.

  // read/write the actions required to execute this transaction.
  void Write(Buffer *buf) const;
  bool Read(Buffer *buf);

  // read/write the results of executing this transaction.
  void WriteResult(Buffer *buf) const;
  bool ReadResult(Buffer *buf);

 public:
  // information related to transaction ownership of data.

  // add an operand or action to this transaction. when the transaction
  // finishes this data will be deleted. called automatically by the
  // operand or action constructor, do not call these anywhere else!
  void AddOperand(TOperand *o);
  void AddAction(TAction *a);

  // add a buffer to this transaction. when the transaction is cleared the
  // buffer will be deleted. buffers must not be added more than once,
  // and buffers which will outlive the transaction do not need to be added.
  void AddBuffer(Buffer *b);

  // clones the specified string using a buffer within this transaction.
  // this pointer will last until the transaction is cleared.
  const char* CloneString(const char *str);

  // release all data used by this transaction, resetting the transaction
  // to an empty state. this is idempotent and is also called when the
  // transaction is deleted.
  void Clear();

 public:
  // information related to the transaction's construction.

  // get the index of an unused variable for this transaction.
  // is_return indicates whether this is a return variable and its value
  // can be queried after the transaction finishes. only variables which
  // whose value will actually be used should have is_return set, as for
  // remote analysis the values of all return variables are transmitted
  // from the manager to the client which submitted the transaction.
  size_t MakeVariable(bool is_return = false);

 public:
  // information related to the transaction's execution.

  // assigns a value to the specified variable,
  // overwriting any previous value.
  void Assign(size_t var, TOperand *value);

  // gets the value associated with a return variable, NULL if the variable
  // was never assigned. if required is set, fails if the variable
  // has not been assigned to.
  TOperand* Lookup(size_t var, bool required = true);

  // Lookup specialized to different types of operands.
  // fail if the variable was not set to the specified type.
  TOperandList*     LookupList(size_t var, bool required = true);
  TOperandString*   LookupString(size_t var, bool required = true);
  TOperandBoolean*  LookupBoolean(size_t var, bool required = true);
  TOperandInteger*  LookupInteger(size_t var, bool required = true);

 private:

  // main actions this transaction executes. these are included in the
  // m_owned_actions list.
  Vector<TAction*> m_actions;

  // whether this is an initial/final transaction.
  bool m_initial;
  bool m_final;

  // whether this transaction has executed.
  bool m_has_executed;

  // whether the transaction succeeded.
  bool m_success;

  struct VariableInfo {
    bool is_return;   // is this a return variable?
    TOperand *value;  // current value of the variable.
    VariableInfo() : is_return(false), value(NULL) {}
  };

  // values of the variables in this transaction, indexed by the variable id.
  Vector<VariableInfo> m_variables;

  // data this transaction owns. these will be deleted when the transaction
  // is deleted or is cleared.
  Vector<TOperand*> m_owned_operands;
  Vector<TAction*> m_owned_actions;
  Vector<Buffer*> m_owned_buffers;
};

extern ConfigOption timeout;
extern ConfigOption trans_remote;
extern ConfigOption trans_initial;

// setup any data structures for transaction submission and error recovery,
// and determine whether transactions will be executed locally or remotely.
// must be called before submitting a transaction.
void AnalysisPrepare(const char *remote_address = NULL);

// return whether submitted transactions are piped to another machine or
// process for execution.
bool IsAnalysisRemote();

// close and clean up any resources used during transaction processing.
void AnalysisCleanup();

// do analysis cleanup and exit the program with the specified code.
void AnalysisFinish(int code);

// get the hard timeout specified at the command line, 0 for no timeout.
uint32_t GetTimeout();

// reset the hard timeout for a new analysis unit. offset indicates any
// additional seconds to pad the user timeout with.
void ResetTimeout(uint32_t offset = 0);

// execute the transaction, either locally or by sending it to a manager
// and blocking until the result is received.
void SubmitTransaction(Transaction *t);

// execute an empty initial or final transaction.
// this is a nop if transactions are not executed remotely.
void SubmitInitialTransaction();
void SubmitFinalTransaction();

NAMESPACE_XGILL_END
