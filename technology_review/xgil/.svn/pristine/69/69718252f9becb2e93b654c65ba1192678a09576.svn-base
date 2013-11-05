
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

// main path-exploration based assertion checker.

#include "frame.h"

NAMESPACE_XGILL_BEGIN

extern ConfigOption checker_verbose;
extern ConfigOption checker_depth;

// check that the specified assertion holds at its indicated point in the
// corresponding CFG. if the result was not a successful check
// then the state where the report was generated will be returned,
// with its m_path filled in.
CheckerState* CheckAssertion(BlockId *id, const AssertInfo &info);

NAMESPACE_XGILL_END
