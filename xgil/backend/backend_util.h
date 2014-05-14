
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

// backend for basic utility functions on integers, lists, etc.

#include "backend.h"

NAMESPACE_XGILL_BEGIN

extern TransactionBackend backend_Util;

NAMESPACE_BEGIN(Backend)

// Integer comparison functions

TAction* ValueLess(Transaction *t,
                   TOperand *v0, TOperand *v1,
                   size_t var_result);

TAction* ValueLessEqual(Transaction *t,
                        TOperand *v0, TOperand *v1,
                        size_t var_result);

TAction* ValueEqual(Transaction *t,
                    TOperand *v0, TOperand *v1,
                    size_t var_result);

// String functions

// input must be a NULL-terminated string. returns whether its length is 0.
TAction* StringIsEmpty(Transaction *t, TOperand *str,
                       size_t var_result);

// List functions

// make an empty list
TAction* ListEmpty(Transaction *t, size_t var_result);

// make a list with the specified elements
TAction* ListCreate(Transaction *t, const Vector<TOperand*> &args,
                    size_t var_result);

// push an element onto the end of an existing list
TAction* ListPush(Transaction *t, TOperand *list, TOperand *arg,
                  size_t var_result);

// Counter functions

// counters which transactions can increment, decrement, or get the value of.
// these can be used by multiple cores doing analysis to synchronize with
// one another: each core can increment the counter when starting
// a computation, decrement it when finishing, and knows all cores
// have finished the computation when the counter becomes zero.

// increment/decrement a global counter.
TAction* CounterInc(Transaction *t, const char *name);
TAction* CounterDec(Transaction *t, const char *name);

// get the value of a counter.
TAction* CounterValue(Transaction *t, const char *name, size_t var_result);

// File functions

// read an entire file's contents into the result variable.
// the result will be the empty string if the file does not exist.
TAction* FileRead(Transaction *t, const char *name, size_t var_result);

NAMESPACE_END(Backend)

NAMESPACE_XGILL_END
