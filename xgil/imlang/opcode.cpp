
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

#include "opcode.h"

NAMESPACE_XGILL_BEGIN

const char* UnopString(UnopKind unop_kind, bool is_ui)
{
  switch (unop_kind) {
  case U_Coerce:       return is_ui ? "" : "()";
  case U_Neg:          return "-";
  case U_BitwiseNot:   return "~";
  case U_LogicalNot:   return "!";
  default:             return NULL;
  }
}

const char* BinopString(BinopKind binop_kind, bool is_ui)
{
  switch (binop_kind) {

  case B_Plus:           return "+";
  case B_Minus:          return "-";
  case B_Mult:           return "*";
  case B_Div:            return "/";
  case B_Mod:            return "%";
  case B_ShiftLeft:      return "<<";
  case B_ShiftRight:     return ">>";
  case B_BitwiseAnd:     return "&";
  case B_BitwiseOr:      return "|";
  case B_BitwiseXOr:     return "^";

  case B_Min:            return "min";
  case B_Max:            return "max";
  case B_DivExact:       return "divx";

  case B_PlusPI:         return "+p";
  case B_MinusPI:        return "-p";

  case B_MinusPP:        return is_ui ? "-" : "-pp";

  case B_LessThan:       return "<";
  case B_GreaterThan:    return ">";
  case B_LessEqual:      return "<=";
  case B_GreaterEqual:   return ">=";
  case B_Equal:          return "==";
  case B_NotEqual:       return "!=";

  case B_LessThanP:      return is_ui ? "<" : "<p";
  case B_GreaterThanP:   return is_ui ? ">" : ">p";
  case B_LessEqualP:     return is_ui ? "<=" : "<=p";
  case B_GreaterEqualP:  return is_ui ? ">=" : ">=p";
  case B_EqualP:         return is_ui ? "==" : "==p";
  case B_NotEqualP:      return is_ui ? "!=" : "!=p";

  case B_LogicalAnd:     return "&&";
  case B_LogicalOr:      return "||";

  default:               return NULL;
  }
}

const char* BoundString(BoundKind bound)
{
  switch (bound) {
  case BND_Lower:   return "lbound";
  case BND_Upper:   return "ubound";
  case BND_Offset:  return "offset";
  default:          Assert(false);
  }
}

const char* DirectiveString(DirectiveKind directive)
{
  switch (directive) {
  case DIRECTIVE_SkipInference: return "skip_inference";
  default: Assert(false);
  }
}

static inline void FoldBoolean(mpz_t res, bool val)
{
  if (val)
    mpz_set_si(res, 1);
  else
    mpz_set_si(res, 0);
}

void ConstFoldUnop(UnopKind kind, const mpz_t val, mpz_t res)
{
  switch (kind) {
  case U_Coerce:
    mpz_set(res, val);
    break;
  case U_Neg:
    mpz_neg(res, val);
    break;
  case U_BitwiseNot:
    mpz_com(res, val);
    break;
  case U_LogicalNot:
    FoldBoolean(res, mpz_cmp_si(val, 0) == 0);
    break;
  default:
    logout << "ERROR: ConstFoldUnop: Unexpected "
           << UnopString(kind) << " " << val << endl;
    Assert(false);
  }
}

void ConstFoldBinop(BinopKind kind,
                    const mpz_t left_val, const mpz_t right_val, mpz_t res)
{
  switch (kind) {

  case B_Plus:
    mpz_add(res, left_val, right_val);
    break;

  case B_Minus:
  case B_MinusPP: // TODO: include scaling here?
    mpz_sub(res, left_val, right_val);
    break;

  case B_Mult:
    mpz_mul(res, left_val, right_val);
    break;

  case B_Div:
  case B_DivExact:  // treat like regular division during folding.
    // leave zero value for division by zero.
    if (mpz_cmp_si(right_val, 0) != 0)
      mpz_fdiv_q(res, left_val, right_val);
    break;

  case B_Mod:
    // ditto for modulus by zero or negative values.
    if (mpz_cmp_si(right_val, 0) > 0)
      mpz_fdiv_r(res, left_val, right_val);
    break;

  case B_ShiftLeft:
    // ditto for left shifts by negative or large values.
    if (mpz_cmp_si(right_val, 0) >= 0 &&
        mpz_cmp_si(right_val, 64) <= 0)
      mpz_mul_2exp(res, left_val, mpz_get_ui(right_val));
    break;

  case B_ShiftRight:
    // ditto for right shifts by negative values or large values.
    if (mpz_cmp_si(right_val, 0) >= 0 &&
        mpz_cmp_si(right_val, 64) <= 0)
      mpz_tdiv_q_2exp(res, left_val, mpz_get_ui(right_val));
    break;

  case B_BitwiseAnd:
    mpz_and(res, left_val, right_val);
    break;

  case B_BitwiseOr:
    mpz_ior(res, left_val, right_val);
    break;

  case B_BitwiseXOr:
    mpz_xor(res, left_val, right_val);
    break;

  case B_Min:
    if (mpz_cmp(left_val, right_val) < 0)
      mpz_set(res, left_val);
    else
      mpz_set(res, right_val);
    break;

  case B_Max:
    if (mpz_cmp(left_val, right_val) > 0)
      mpz_set(res, left_val);
    else
      mpz_set(res, right_val);
    break;

  case B_LessThan:
  case B_LessThanP:
    FoldBoolean(res, mpz_cmp(left_val, right_val) < 0);
    break;

  case B_GreaterThan:
  case B_GreaterThanP:
    FoldBoolean(res, mpz_cmp(left_val, right_val) > 0);
    break;

  case B_LessEqual:
  case B_LessEqualP:
    FoldBoolean(res, mpz_cmp(left_val, right_val) <= 0);
    break;

  case B_GreaterEqual:
  case B_GreaterEqualP:
    FoldBoolean(res, mpz_cmp(left_val, right_val) >= 0);
    break;

  case B_Equal:
  case B_EqualP:
    FoldBoolean(res, mpz_cmp(left_val, right_val) == 0);
    break;

  case B_NotEqual:
  case B_NotEqualP:
    FoldBoolean(res, mpz_cmp(left_val, right_val) != 0);
    break;

  case B_LogicalAnd:
    FoldBoolean(res, mpz_cmp_si(left_val, 0) != 0 &&
                     mpz_cmp_si(right_val, 0) != 0);
    break;

  case B_LogicalOr:
    FoldBoolean(res, mpz_cmp_si(left_val, 0) != 0 ||
                     mpz_cmp_si(right_val, 0) != 0);
    break;

  default:
    logout << "ERROR: ConstFoldBinop: Unexpected "
           << BinopString(kind)
           << " " << left_val << " " << right_val << endl;
    Assert(false);
  }
}

NAMESPACE_XGILL_END
