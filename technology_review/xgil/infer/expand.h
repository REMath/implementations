
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

// rules for determining when expressions are expandable in the callees
// and callers of a function.

#include <memory/mblock.h>
#include <imlang/trace.h>

NAMESPACE_XGILL_BEGIN

// whether exp/bit can be expanded in its callers. is_function indicates
// whether this is for a function vs. loop.
bool UseCallerExp(Exp *exp, bool is_function);
bool UseCallerBit(Bit *bit, bool is_function);

// whether exp should be expanded in some callee. if so, returns the point
// where the exp should be expanded.
PPoint UseCalleeExp(Exp *exp);

// get an exp/bit expressed in terms of the exit from a callee equivalent
// to exp/bit. any subexpressions which cannot be represented in terms of the
// callee exit state will be converted using ExpFrame on caller_frame_id.
Exp* TranslateCalleeExp(BlockMemory *mcfg, PPoint point, Exp *exp,
                        FrameId caller_frame_id);
Bit* TranslateCalleeBit(BlockMemory *mcfg, PPoint point, Bit *bit,
                        FrameId caller_frame_id);

// return whether reads/writes to lval can be treated as part of a global or
// type invariant. in the type invariant case, store the type and base lval
// in pcsu and pcsu_lval.
bool UseHeapExp(Exp *exp, TypeCSU **pcsu, Exp **pcsu_lval);

// get an exp/bit based on new_lval from an exp/bit based on old_lval.
// for a purely global exp/bit then old_lval and new_lval may be NULL.
// if use_exit is specified then ExpExit will be used instead of ExpDereference
// where appropriate.
Exp* TranslateHeapExp(Exp *old_lval, Exp *new_lval, bool use_exit, Exp *exp);
Bit* TranslateHeapBit(Exp *old_lval, Exp *new_lval, bool use_exit, Bit *bit);

// other expansion utility

// mapper to convert a point-relative expression in the callee's space to
// a point-relative expression at the callsite, e.g. replacing
// each __argN* with the actual argument expression passed in.
class ConvertCallsiteMapper : public ExpMapper
{
public:
  BlockCFG *cfg;
  PPoint point;
  bool unrolling;

  ConvertCallsiteMapper(BlockCFG *_cfg, PPoint _point, bool _unrolling)
    : ExpMapper(VISK_All, WIDK_Drop),
      cfg(_cfg), point(_point), unrolling(_unrolling)
  {}

  Exp* Map(Exp *value, Exp *old);
};

NAMESPACE_XGILL_END
