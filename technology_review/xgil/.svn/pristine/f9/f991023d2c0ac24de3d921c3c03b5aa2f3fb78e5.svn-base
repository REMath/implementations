
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

// opcodes for arithmetic operations.

#include "interface.h"
#include <util/buffer.h>

NAMESPACE_XGILL_BEGIN

enum UnopKind {
  U_Invalid = 0,

#define XIL_FILL_UNOP(NAME, VALUE)  U_ ## NAME = VALUE,
  XIL_ITERATE_UNOP(XIL_FILL_UNOP)
#undef XIL_FILL_UNOP

};

enum BinopKind {
  B_Invalid = 0,

#define XIL_FILL_BINOP(NAME, VALUE)  B_ ## NAME = VALUE,
  XIL_ITERATE_BINOP(XIL_FILL_BINOP)
#undef XIL_FILL_BINOP

};

// integral properties of a memory address.
enum BoundKind {
  BND_Invalid = 0,

  BND_Lower = 1,
  BND_Upper = 2,
  BND_Offset = 3,
};

// directives that can be specified in annotations.
enum DirectiveKind {
  // when used in a type or global invariant, indicates that during checking
  // the analysis should not try to infer invariants on the type or global.
  DIRECTIVE_SkipInference = 0
};

// get the string representation of an operation. these return NULL
// rather than failing on an invalid kind. is_ui indicates whether
// this is printing for the UI.
const char* UnopString(UnopKind kind, bool is_ui = false);
const char* BinopString(BinopKind kind, bool is_ui = false);

// get the string representation of an absolute buffer bound.
const char* BoundString(BoundKind kind);

// get the string representation of a directive.
const char* DirectiveString(DirectiveKind kind);

// constant fold an operation over particular integers.
void ConstFoldUnop(UnopKind kind, const mpz_t val, mpz_t res);
void ConstFoldBinop(BinopKind kind,
                    const mpz_t left_val, const mpz_t right_val, mpz_t res);

// whether the specified binop requires a stride type.
static inline bool IsPointerBinop(BinopKind kind)
{
  switch (kind) {
  case B_PlusPI:
  case B_MinusPI:
  case B_MinusPP:
  case B_LessThanP:
  case B_GreaterThanP:
  case B_LessEqualP:
  case B_GreaterEqualP:
  case B_EqualP:
  case B_NotEqualP:
    return true;
  default:
    return false;
  }
}

// get the non-pointer binop for the specified binop. this is only performed
// for binops which take pointers for both their operands (MinusPP and the
// pointer comparison binops).
static inline BinopKind NonPointerBinop(BinopKind kind)
{
  switch (kind) {
  case B_MinusPP:        return B_Minus;
  case B_LessThanP:      return B_LessThan;
  case B_GreaterThanP:   return B_GreaterThan;
  case B_LessEqualP:     return B_LessEqual;
  case B_GreaterEqualP:  return B_GreaterEqual;
  case B_EqualP:         return B_Equal;
  case B_NotEqualP:      return B_NotEqual;
  default:               return kind;
  }
}

// inverse of NonPointerBinop for any binops which have a pointer version.
static inline BinopKind PointerBinop(BinopKind kind)
{
  switch (kind) {
  case B_Minus:         return B_MinusPP;
  case B_LessThan:      return B_LessThanP;
  case B_GreaterThan:   return B_GreaterThanP;
  case B_LessEqual:     return B_LessEqualP;
  case B_GreaterEqual:  return B_GreaterEqualP;
  case B_Equal:         return B_EqualP;
  case B_NotEqual:      return B_NotEqualP;
  default:              return kind;
  }
}

// whether the specified binop is a comparison binop.
static inline bool IsCompareBinop(BinopKind kind)
{
  switch (kind) {
  case B_LessThan:
  case B_GreaterThan:
  case B_LessEqual:
  case B_GreaterEqual:
  case B_Equal:
  case B_NotEqual:
  case B_LessThanP:
  case B_GreaterThanP:
  case B_LessEqualP:
  case B_GreaterEqualP:
  case B_EqualP:
  case B_NotEqualP:
    return true;
  default:
    return false;
  }
}

// get the negated binop b' of b such that (v b' o) iff !(v b o).
static inline BinopKind NegateCompareBinop(BinopKind kind)
{
  switch (kind) {
  case B_LessThan:       return B_GreaterEqual;
  case B_GreaterThan:    return B_LessEqual;
  case B_LessEqual:      return B_GreaterThan;
  case B_GreaterEqual:   return B_LessThan;
  case B_Equal:          return B_NotEqual;
  case B_NotEqual:       return B_Equal;
  case B_LessThanP:      return B_GreaterEqualP;
  case B_GreaterThanP:   return B_LessEqualP;
  case B_LessEqualP:     return B_GreaterThanP;
  case B_GreaterEqualP:  return B_LessThanP;
  case B_EqualP:         return B_NotEqualP;
  case B_NotEqualP:      return B_EqualP;
  default:               return B_Invalid;
  }
}

// whether the specified binop is a bitwise binop.
static inline bool IsBitwiseBinop(BinopKind kind)
{
  switch (kind) {
  case B_BitwiseAnd:
  case B_BitwiseOr:
  case B_BitwiseXOr:
    return true;
  default:
    return false;
  }
}

// whether the specified binop is a logical binop.
static inline bool IsLogicalBinop(BinopKind kind)
{
  switch (kind) {
  case B_LogicalAnd:
  case B_LogicalOr:
    return true;
  default:
    return false;
  }
}

// is (v b o) equivalent to (o b v)?
static inline bool IsCommutativeBinop(BinopKind kind)
{
  switch (kind) {
  case B_Plus:
  case B_Mult:
  case B_BitwiseAnd:
  case B_BitwiseOr:
  case B_BitwiseXOr:
  case B_Equal:
  case B_NotEqual:
  case B_EqualP:
  case B_NotEqualP:
  case B_LogicalAnd:
  case B_LogicalOr:
    return true;
  default:
    return false;
  }
}

// get the reversed binop b' of b such that (v b' o) is equivalent to (o b v).
static inline BinopKind ReverseBinop(BinopKind kind)
{
  if (IsCommutativeBinop(kind))
    return kind;

  switch (kind) {
  case B_LessThan:       return B_GreaterThan;
  case B_GreaterThan:    return B_LessThan;
  case B_LessEqual:      return B_GreaterEqual;
  case B_GreaterEqual:   return B_LessEqual;
  case B_LessThanP:      return B_GreaterThanP;
  case B_GreaterThanP:   return B_LessThanP;
  case B_LessEqualP:     return B_GreaterEqualP;
  case B_GreaterEqualP:  return B_LessEqualP;
  default:               return B_Invalid;
  }
}

NAMESPACE_XGILL_END
