
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

// functionality for inferring loop and function invariants.

#include "infer.h"

NAMESPACE_XGILL_BEGIN

extern ConfigOption print_invariants;

// intermediate state computed for invariant inference which will also
// be used for demand-driven sufficient condition inference.

// potential comparisons between expressions.
struct BaseCompare
{
  // test this comparison was derived from.
  Exp *test;

  // comparison binop between source and target.
  BinopKind kind;

  // must be an lvalue or analysis expression.
  Exp *source;

  // may be an arbitrary expression.
  Exp *target;

  // stride type for pointer comparisons.
  Type *stride_type;

  BaseCompare()
    : kind(B_Invalid), source(NULL), target(NULL), stride_type(NULL)
  {}

  BaseCompare(Exp *_test, BinopKind _kind,
              Exp *_source, Exp *_target, Type *_stride_type)
    : test(_test), kind(_kind),
      source(_source), target(_target), stride_type(_stride_type)
  {}

  bool operator == (const BaseCompare &o) const {
    return test == o.test && kind == o.kind
      && source == o.source && target == o.target
      && stride_type == o.stride_type;
  }
};

// potential assignment from an rvalue to an lvalue.
struct BaseAssign
{
  // left side of the assignment.
  Exp *left;

  // right side of the assignment.
  Exp *right;

  BaseAssign()
    : left(NULL), right(NULL)
  {}

  BaseAssign(Exp *_left, Exp *_right)
    : left(_left), right(_right)
  {}
};

// get all the comparisons used in the specified bit. only looks at the
// phase of the comparisons, not disjunctions/conjunctions involved.
void GetBaseCompares(BlockMemory *mcfg, Bit *bit,
                     Vector<BaseCompare> *compares,
                     bool ignore_disjunction = false);

// get additional implicit comparisons from operations such as %, &, and max.
void GetExtraCompares(Bit *bit, Vector<BaseCompare> *compares);

// converts a list of comparisons on any comparison binop into a list
// of comparisons on just equality ==/<=/>= binops.
void GetCompareEqualities(const Vector<BaseCompare> &compares,
                          Vector<BaseCompare> *equality_compares);

// clears out the specified list of comparisons.
void ClearCompareList(Vector<BaseCompare> *compares);

// invariant inference.

// invariant inference is done with the guess and check method,
// in the same way we do loop sufficient condition inference in
// solve/sufficient.h. a bit is a loop invariant if it holds at entry
// and exit to every iteration of the loop. to test a bit to tell whether
// it is a loop invariant, then, we try the following tests:
//
// - Assert the bit's negation at entry to the loop parent. if this is
//   satisfiable it is not a loop invariant.
// - Assert the bit at entry to the loop body, and the bit's negation
//   at exit from the loop body. if this is satisfiable it is not a
//   loop invariant.

// invariant inference for functions just relates the values written by the
// function (most commonly the return value) with the entry state
// or with constants.

// infer loop or function invariants for the specified summary.
void InferInvariants(BlockSummary *sum, const Vector<Exp*> &arithmetic_list);

NAMESPACE_XGILL_END
