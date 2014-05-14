
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

// functionality for inferring sufficient conditions to disprove an
// error occurring within a loop.

#include "propagate.h"

NAMESPACE_XGILL_BEGIN

extern ConfigOption checker_sufficient;

// if possible, get a bit such that if the bit holds within frame then
// the error condition is unsatisfiable --- the bit implies the original
// assertion and is thus stronger than that assertion. thus, if we can
// get a sufficient condition and show the sufficient condition always
// holds (its negation is unsatisfiable), we show the assertion itself
// always holds. if we find a counterexample to the sufficient condition,
// we still need to see if the original assertion holds, but if we picked
// a good sufficient condition then the counterexample itself should
// quickly lead to a counterexample on that original assertion.

// the most important property of the sufficient condition is that it
// has no dependencies on the variables which change during the loop.
// thus we can lift it out of the loop and not have to worry about how
// many iterations run before the error is exposed.

// example:
//
// for (i = 0; i < n; i++) {
//   buf[i] = 0;
// }
//
// there is an error if SAT(guard && !assert_cond)
// a condition is sufficient if !SAT(guard && !assert_cond && suff_cond)
//
// assert_cond: i < ubound(buf)
// guard: i < n
//
// the condition n <= ubound(buf) is sufficient:
//   SAT(i < n && !(i < ubound(buf)) && n <= ubound(buf)) = false
//
// now we have to find a counterexample where SAT(!(n <= ubound(buf))).
// since n and ubound(buf) do not change during the loop we don't have
// to unroll loop iterations. if we can't find a counterexample then
// the original error cannot occur.

// 'false' is always a sufficient condition, just never a useful one,
// so we won't return it.

// indicates whether a bit is preserved by the modifications in a loop body.
bool IsLoopBitPreserved(CheckerFrame *frame, Bit *bit);

// searches for sufficient bits for safe_bit, filling in the sufficient lists
// in propagate with all tested and successful bits. propagate_list will be
// filled in with propagations for each sufficient condition found.
void GetSufficientConditions(CheckerPropagate *propagate, Bit *safe_bit,
                             Vector<CheckerPropagate*> *propagate_list);

NAMESPACE_XGILL_END
