
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

// tags and layout for all memory analysis data structures.

///////////////////////////////
// Callgraph
///////////////////////////////

// children:
//   TAG_CacheString
//   TAG_True / TAG_False (for callers)
//   list of TAG_CAllEdge
#define TAG_CallEdgeSet 3040

// children:
//   TAG_BlockPPoint
//   TAG_CacheString
//   TAG_Exp (optional)
#define TAG_CallEdge 3042

///////////////////////////////
// Escape
///////////////////////////////

// children:
//   TAG_LocTrace
//   TAG_True / TAG_False (for forward)
//   list of TAG_EscapeEdge
#define TAG_EscapeEdgeSet 3050

// children:
//   TAG_LocTrace
//   TAG_BlockPPoint
//   TAG_EscapeEdgeMoveCaller
//   TAG_EscapeEdgeMoveCallee
#define TAG_EscapeEdge 3052

// children: None. if present indicates the edge call direction.
#define TAG_EscapeEdgeMoveCaller  3054
#define TAG_EscapeEdgeMoveCallee  3056

// children:
//   TAG_LocTrace
//   list of TAG_EscapeAccess
#define TAG_EscapeAccessSet 3060

// children:
//   TAG_Kind
//   TAG_LocTrace
//   TAG_BlockPPoint
//   TAG_Field (fld, rfld)
#define TAG_EscapeAccess 3062

///////////////////////////////
// BlockMemory
///////////////////////////////

// children:
//   TAG_BlockId
//   TAG_MemorySimplify
//   TAG_MemoryAlias
//   TAG_MemoryClobber
//   list of TAG_MemoryGuardEntry
//   list of TAG_MemoryEdgeCondEntry
//   list of TAG_MemoryReturnEntry
//   list of TAG_MemoryTargetEntry
//   list of TAG_MemoryAssignEntry
//   list of TAG_MemoryArgumentEntry
//   list of TAG_MemoryClobberEntry
//   list of TAG_MemoryGCEntry
#define TAG_BlockMemory  3100

// children: TAG_UInt32
#define TAG_MemoryKindSimplify  3110
#define TAG_MemoryKindAlias     3112
#define TAG_MemoryKindClobber   3114
#define TAG_MemoryGCEntry       3116

// children:
//   TAG_Index
//   TAG_Bit
#define TAG_MemoryGuardEntry  3120

// children:
//   TAG_Index
//   TAG_Bit x2
#define TAG_MemoryAssumeEntry  3122

// children:
//   TAG_Index
//   TAG_Exp
//   TAG_Bit
#define TAG_MemoryReturnEntry  3124

// children:
//   TAG_Index
//   TAG_Exp
//   TAG_Bit
#define TAG_MemoryTargetEntry  3126

// children:
//   TAG_Index
//   TAG_Exp x2 or x3  (left, right, kind?)
//   TAG_Bit
#define TAG_MemoryAssignEntry  3128
#define TAG_MemoryArgumentEntry  3130
#define TAG_MemoryClobberEntry  3132

///////////////////////////////
// BlockModset
///////////////////////////////

// children:
//   TAG_BlockId
//   list of TAG_Exp
//   list of TAG_MemoryAssignEntry (with point index 0)
#define TAG_BlockModset  3200

// children:
//   TAG_Exp x1 or x2  (lvalue, kind?)
#define TAG_ModsetEntry  3202

// children:
//   TAG_Exp x2  (left, right)
//   TAG_Bit
#define TAG_ModsetAssign  3204

// children: none
#define TAG_ModsetCanGC  3206

///////////////////////////////
// BlockSummary
///////////////////////////////

// children:
//   TAG_BlockId
//   list of TAG_SummaryAssert
//   list of TAG_SummaryAssume
#define TAG_BlockSummary  3500

// children:
//   TAG_Kind
//   TAG_OpCode
//   TAG_Index
//   TAG_Bit
#define TAG_SummaryAssert  3512

// children:
//   TAG_Bit
#define TAG_SummaryAssume  3516
