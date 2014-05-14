
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

#include "infer.h"

// functions for inferring conditions related to establishing or identifying
// the positions of NULL terminators and other kinds of terminators.
// this does *not* include inference of loop invariants related to termination;
// see invariant.cpp for that.

NAMESPACE_XGILL_BEGIN

struct TerminatorInfo
{
  // base lvalue the terminator test is relative to.
  Exp *target;

  // termination test being identified.
  Exp *terminate_test;
  ExpInt *terminate_int;

  TerminatorInfo()
    : target(NULL), terminate_test(NULL), terminate_int(NULL)
  {}

  TerminatorInfo(Exp *_target, Exp *_terminate_test, ExpInt *_terminate_int)
    : target(_target), terminate_test(_terminate_test),
      terminate_int(_terminate_int)
  {}

  bool operator == (const TerminatorInfo &o) const {
    return target == o.target
      && terminate_test == o.terminate_test
      && terminate_int == o.terminate_int;
  }
};

// fill in terminators with any traces and associated terminator tests that
// might be performed by sum.
void InferTerminatorTests(BlockSummary *sum,
                          const Vector<Exp*> &arithmetic_list,
                          Vector<TerminatorInfo> *terminators);

// get the candidate loop invariant to use when determining if target
// is always terminated according to the specified kind within a loop.
Bit* GetTerminatorInvariant(Type *stride_type, Exp *target, Exp *init_target,
                            Exp *terminate_test, ExpInt *terminate_int);

NAMESPACE_XGILL_END
