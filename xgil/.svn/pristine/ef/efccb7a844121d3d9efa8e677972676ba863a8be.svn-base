
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

// tags and layout for all transaction data structures

///////////////////////////////
// TOperand
///////////////////////////////

// children:
//   TAG_Kind (all)
//   TAG_Index (variable, integer)
//   TAG_True / TAG_False (boolean)
//   TAG_String (string)
//   ordered list of TAG_TOperand (list)
#define TAG_TOperand 500

///////////////////////////////
// TAction
///////////////////////////////

// children:
//   TAG_Kind (all)
//   TAG_Index (assign, call, iterate)
//   TAG_Name (call)
//   TAG_True / TAG_False (test)
//   single TAG_TOperand (assign, test, iterate)
//   ordered list of TAG_TOperand (call)
//   ordered list of TAG_TAction (sequence, test, iterate)
#define TAG_TAction 520

///////////////////////////////
// Transaction
///////////////////////////////

// children:
//   TAG_TAction*
//   TAG_TransactionInitial
//   TAG_TransactionFinal
//   list of TAG_TransactionVariable (return vars only)
#define TAG_Transaction 530

// children: none
#define TAG_TransactionInitial 532
#define TAG_TransactionFinal   534

// children:
//   TAG_True / TAG_False (for success)
//   ordered list of TAG_TransactionVariable (return vars only)
#define TAG_TransactionResult 540

// children:
//   TAG_Index
//   TAG_TOperand (only used for TAG_TransactionResult)
#define TAG_TransactionVariable 550
