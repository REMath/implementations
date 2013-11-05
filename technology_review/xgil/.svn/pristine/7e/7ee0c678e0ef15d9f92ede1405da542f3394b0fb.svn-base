
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

#include "block.h"

NAMESPACE_XGILL_BEGIN

// copy the begin/end locations and declared variables from old_cfg to new_cfg.
void CopyCFGLocationsVariables(BlockCFG *old_cfg, BlockCFG *new_cfg);

// copy the points, edges, and loop heads from old_cfg to new_cfg.
// this plus CopyLocationsVariables covers all data in an initial CFG
// besides the block identifier.
void CopyCFGPointsEdges(BlockCFG *old_cfg, BlockCFG *new_cfg);

// trim away points and edges from cfg for which either there is no path from
// the entry point, or no path to the exit point. if flatten_skips is set,
// flattens away any Skip() edges from the final CFG. consumes a reference
// on new_id. TODO: this currently trims away paths that loop infinitely. fix?
void TrimUnreachable(BlockCFG *cfg, bool flatten_skips);

// reorganize the points in CFG so that their order forms a topological sort.
// the CFG should already have had unreachable points trimmed and skip
// edges followed.
void TopoSortCFG(BlockCFG *cfg);

// covert a possibly loop containing CFG for some function into a list
// of equivalent loop-free CFGs for the function and its various loops.
// also removes Skip edges from the result CFGs.
void SplitLoops(BlockCFG *cfg, Vector<BlockCFG*> *resultCFGs);

NAMESPACE_XGILL_END
