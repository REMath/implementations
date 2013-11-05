
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

#include "interface.h"
#include <util/buffer.h>

// tags and layout for all intermediate language data structures

// all children are given in the order they should be appear in
// the stream. children are required unless otherwise specified

///////////////////////////////
// Type
///////////////////////////////

// children:
//   TAG_Kind (all)
//   TAG_Width (all)
//   TAG_Sign (all)
//   TAG_Name (csu)
//   TAG_Type (pointer, array, function)
//   TAG_Count (array)
//   TAG_TypeFunctionCSU (function)
//   TAG_TypeFunctionVarArgs (function)
//   TAG_TypeFunctionArguments (function)
#define TAG_Type  1100

// children: none. if present the function is varargs
#define   TAG_TypeFunctionVarArgs  1102

// children: ordered list of TAG_Type for argument types
#define   TAG_TypeFunctionArguments  1104

// children: TAG_Type
#define   TAG_TypeFunctionCSU  1106

///////////////////////////////
// CompositeCSU and Field
///////////////////////////////

// children:
//   TAG_Kind
//   TAG_Name
//   TAG_Width
//   TAG_Command (optional)
//   TAG_Location x2
//   list of TAG_CSUBaseClass
//   list of TAG_DataField
//   list of TAG_FunctionField
#define TAG_CompositeCSU  1200

// children: TAG_String
#define   TAG_CSUBaseClass  1202
#define   TAG_Command  1204

// children:
//   TAG_Name
//   TAG_Type
//   TAG_FieldCSU
//   TAG_FieldInstanceFunction
//   TAG_FieldVirtual
//   TAG_FieldCtor
//   there may be a second TAG_Name for the source name of the field.
#define TAG_Field  1210

// children: TAG_Type for the parent CSU type
#define   TAG_FieldCSU  1212

// children: none. if present the field is an instance function.
#define   TAG_FieldInstanceFunction  1214

// children:
//   TAG_Field
//   TAG_Offset
#define TAG_DataField  1218

// children:
//   TAG_Field
//   TAG_Variable
#define TAG_FunctionField  1220

///////////////////////////////
// Variable
///////////////////////////////

// children:
//   TAG_Kind (all)
//   TAG_Name (global, func, arg, local, temp)
//   TAG_Index (arg)
//   TAG_BlockId (any non-global ?)
//   there may be a second TAG_Name for the source name of the variable.
#define TAG_Variable  1300

///////////////////////////////
// Exp
///////////////////////////////

// children:
//   TAG_Kind (all)
//   TAG_Width (all)
//   TAG_ExpUnsigned (all)
//   TAG_Exp (most)
//   TAG_Variable (variable)
//   TAG_Field (fld, rfld)
//   TAG_Type (index, string, ptr binop, bound, terminator)
//   TAG_String (string, int, float)
//   TAG_OpCode (unop, binop, bound, annotate)
//   TAG_Index (vptr, clobber, val, guard)
//   TAG_Location (clobber)
//   TAG_True / TAG_False (val, for relative)
#define TAG_Exp  1400

// children: none (if present the expression is unsigned)
#define TAG_ExpUnsigned  1402

///////////////////////////////
// Trace
///////////////////////////////

// children:
//   TAG_Kind (all)
//   TAG_Exp (all)
//   TAG_Variable (func)
//   TAG_Name (comp)
//   ordered list of TAG_BlockPPoint (func)
#define TAG_Trace  1450

///////////////////////////////
// Block
///////////////////////////////

// children:
//   TAG_Kind (all)
//   TAG_Variable (all)
//   TAG_String (loop)
#define TAG_BlockId  1610

// children: TAG_BlockId, TAG_Index, TAG_Version
#define TAG_BlockPPoint  1612

// children: TAG_UInt32
#define TAG_Version  1614

// children: TAG_Variable, TAG_Type
#define TAG_DefineVariable  1618

// children: TAG_Location
#define TAG_PPoint  1620

// children: TAG_Index, TAG_Location (optional)
#define TAG_LoopHead  1622

// children: TAG_Index
#define TAG_LoopIsomorphic  1624

// children: TAG_Index, TAG_BlockId
#define TAG_PointAnnotation  1626

// children:
//   TAG_Kind (all)
//   TAG_Index (all x2)
//   TAG_PEdgeAssumeNonZero (assume)
//   TAG_Exp (assume, assign x2, call x1 or x2)
//   TAG_PEdgeCallArguments (call)
//   TAG_PEdgeCallInstance (call optional)
//   TAG_Type (assign, call)
//   TAG_BlockId (loop, annotation)
#define TAG_PEdge  1630

// children: none (if present, the assume is != 0)
#define   TAG_PEdgeAssumeNonZero  1632

// children: ordered list of TAG_Exp
#define   TAG_PEdgeCallArguments  1634

// children: TAG_Exp
#define   TAG_PEdgeCallInstance  1636

// children:
//   TAG_BlockId
//   TAG_Version
//   TAG_Command (optional)
//   TAG_Location x2
//   TAG_Type (instance function only)
//   TAG_Field (instance function only)
//   TAG_Kind (annotation CFGs only)
//   ordered list of TAG_PPoint
//   ordered list of TAG_PEdge
//   TAG_Index x2  (for entry/exit points)
//   list of TAG_DefineVariable
//   list of TAG_BlockPPoint (loop parents)
//   list of TAG_LoopHead
//   list of TAG_LoopIsomorphic
//   list of TAG_PointAnnotation
#define TAG_BlockCFG 1700
