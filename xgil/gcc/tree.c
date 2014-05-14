
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

#include "xgill.h"
#include <tree-iterator.h>
#include <cp/cp-tree.h>
#include <real.h>

// connect the current point for env to any post side effects from post_point.
void XIL_ConnectPostPoint(XIL_PPoint *point, struct XIL_PostEdges post_edges)
{
  if (!post_edges.start_point) {
    // there were no post side effects, so no connecting to do.
    return;
  }

  XIL_CFGEdgeSkip(*point, post_edges.start_point);

  // the edges out of post_point should be a straight line series of edges.
  // the last point in this series is the new current point.
  *point = post_edges.end_point;
}

// do any extra processing indicated by env using the rvalue result
// of translating a tree.
void XIL_ProcessResult(struct XIL_TreeEnv *env, XIL_Exp result)
{
  gcc_assert(result);

  if (!XIL_TreeResultUsed(env))
    return;

  env->processed = true;

  if (env->point && *env->point)
    xil_active_env.last_point = *env->point;

  // figure out what to do with the result according to the environment
  // we're evaluating the expression in.

  if (env->result_branch) {

    // check to see if the branch can be folded away. important for
    // do { ... } while (0); loops and similar constructs.
    long result_value;
    if (XIL_GetExpInt(result, &result_value)) {
      if (result_value)
        XIL_CFGEdgeSkip(*env->point, env->true_point);
      else
        XIL_CFGEdgeSkip(*env->point, env->false_point);
    }
    else {
      XIL_CFGEdgeAssume(*env->point, env->true_point, result, 1);
      XIL_CFGEdgeAssume(*env->point, env->false_point, result, 0);
    }

    *env->point = 0;
    return;
  }

  if (env->result_assign) {
    XIL_Exp assign_rhs = result;

    XIL_PPoint loc_point = *env->point;
    if (!loc_point) loc_point = xil_active_env.last_point;

    XIL_Location loc = XIL_CFGGetPointLocation(loc_point);
    XIL_PPoint after_point = XIL_CFGAddPoint(loc);

    XIL_CFGEdgeAssign(*env->point, after_point,
                      env->result_assign_type, env->result_assign, assign_rhs);
    *env->point = after_point;
    return;
  }

  if (env->result_lval) {
    XIL_Exp address = XIL_ExpAddress(result);

    if (address) {
      *env->result_lval = address;
    }
    else {
      // this should only show up for malformed initial() applications.
      // TODO: need a better way of logging these.
      gcc_assert(xil_has_annotation);
      XIL_Var error_var =
        XIL_VarLocal("__initial_error", "__initial_error", false);

      XIL_Type error_type = XIL_TypeError();
      XIL_CFGAddVar(error_var, error_type, 0);

      *env->result_lval = XIL_ExpVar(error_var);
    }
    return;
  }

  if (env->result_rval) {
    *env->result_rval = result;
    return;
  }

  gcc_unreachable();
}

// get the location for the specified point, updating it to the source
// location of expr if known.
XIL_Location XIL_TryUpdateLocation(XIL_PPoint point, tree node)
{
  XIL_Location loc = NULL;

  if (EXPR_HAS_LOCATION(node)) {
    const char *file = EXPR_FILENAME(node);
    int line = EXPR_LINENO(node);
    loc = XIL_MakeLocation(file, line);

    if (point) {
      XIL_CFGSetPointLocation(point, loc);
      xil_active_env.last_point = point;
    }
  }

  if (loc)
    return loc;

  // don't have a point in the CFG, and don't have a tree with a location.
  return XIL_CFGGetPointLocation(xil_active_env.last_point);
}

const char* XIL_TreeIntString(tree node)
{
  mpz_t mpz;
  mpz_init(mpz);

  tree type = TREE_TYPE(node);
  int unsign = TYPE_UNSIGNED(type);

  double_int cst = TREE_INT_CST(node);
  mpz_set_double_int(mpz, cst, unsign);

  if (unsign) {
    // the wide int may have bits set above the width of the type.
    const char *max = NULL;
    int bits = TYPE_SIZE(type) ?
      TREE_UINT(TYPE_SIZE(type)) : TYPE_PRECISION(type);
    switch (bits) {
    case 8:  max = "255"; break;
    case 16: max = "65535"; break;
    case 32: max = "4294967295"; break;
    case 64: max = "18446744073709551615"; break;
    default: break;
    }
    if (max) {
      mpz_t mask;
      mpz_init_set_str(mask, max, 10);
      mpz_and(mpz, mpz, mask);
    }
  }

  int needed = mpz_sizeinbase(mpz, 10) + 2;
  char *str = xmalloc(needed);

  mpz_get_str(str, 10, mpz);
  gcc_assert(strlen(str) + 1 <= needed);
  mpz_clear(mpz);
  return str;
}

void XIL_TranslateConstant(struct XIL_TreeEnv *env, tree node)
{
  switch (TREE_CODE(node)) {

  case INTEGER_CST: {
    const char *str = XIL_TreeIntString(node);
    XIL_Exp result = XIL_ExpIntStr(str);
    XIL_ProcessResult(env, result);
    return;
  }

  case REAL_CST: {
    struct real_value *value = TREE_REAL_CST_PTR(node);

#define REAL_BUF_SIZE 200

    char *buf = xmalloc(REAL_BUF_SIZE);
    real_to_decimal(buf, value, REAL_BUF_SIZE, 0, 1);

#undef REAL_BUF_SIZE

    XIL_Exp result = XIL_ExpFloat(buf);
    XIL_ProcessResult(env, result);
    return;
  }

  case STRING_CST: {
    tree type = TREE_TYPE(node);
    XIL_Type xil_type = XIL_TranslateType(type);

    void *data = (void*) TREE_STRING_POINTER(node);
    int data_length = TREE_STRING_LENGTH(node);

    XIL_Exp str_exp = XIL_ExpString(xil_type, data, data_length);
    XIL_Exp result = XIL_ExpDrf(str_exp);
    XIL_ProcessResult(env, result);
    return;
  }

  // constant for pointer-to-member.
  case PTRMEM_CST:
    TREE_BOGUS_RESULT(env);

  default:
    TREE_UNEXPECTED_RESULT(env, node);
  }

  gcc_unreachable();
}

void XIL_TranslateDeclaration(struct XIL_TreeEnv *env, tree node)
{
  // watch for enum constants. treat these as their constant value.
  if (TREE_CODE(node) == CONST_DECL) {
    tree initial = DECL_INITIAL(node);
    if (!initial)
      TREE_UNEXPECTED_RESULT(env, node);
    XIL_TranslateTree(env, initial);
    return;
  }

  // if we're processing an annotation file, watch for variables which are
  // fields of the type we are making an invariant for. these are only used
  // for type invariants in C.
  tree attr = DECL_ATTRIBUTES(node);
  while (attr) {
    int value;
    const char *purpose = XIL_DecodeAttribute(attr, NULL, &value);
    if (purpose && !strcmp(purpose, "annot_this_var")) {
      XIL_Var this_var = XIL_VarThis(false);
      XIL_Exp this_exp = XIL_ExpVar(this_var);
      XIL_Exp this_drf = XIL_ExpDrf(this_exp);

      // value is a flag. if nonzero then a field of the 'this' type,
      // if zero then the 'this' type itself.
      if (!value) {
        XIL_ProcessResult(env, this_drf);
        return;
      }

      const char *name = IDENTIFIER_POINTER(DECL_NAME(node));

      gcc_assert(xil_annotation_this);
      const char *csu_name = XIL_CSUName(xil_annotation_this, NULL);
      gcc_assert(csu_name);

      XIL_Type xil_type = XIL_TranslateType(TREE_TYPE(node));
      XIL_Field field = XIL_MakeField(name, name, csu_name, xil_type, false);

      XIL_Exp this_fld = XIL_ExpFld(this_drf, field);
      XIL_Exp result = XIL_ExpDrf(this_fld);

      XIL_ProcessResult(env, result);
      return;
    }
    attr = TREE_CHAIN(attr);
  }

  XIL_Var var = XIL_TranslateVar(node);
  XIL_Exp var_exp = XIL_ExpVar(var);
  XIL_Exp result = XIL_ExpDrf(var_exp);

  // add an extra dereference for variable length-arrays. these are converted
  // to pointers in the generated CFGs.
  tree type = TREE_TYPE(node);
  if (TREE_CODE(type) == ARRAY_TYPE) {
    tree size = TYPE_SIZE_UNIT(type);

    if (size && TREE_CODE(size) != INTEGER_CST) {
      result = XIL_ExpDrf(result);

      // additionally check to make sure this is a local variable of the
      // currently analyzed function.
      if (TREE_CODE(node) != VAR_DECL ||
          DECL_CONTEXT(node) != xil_active_env.decl)
        TREE_UNEXPECTED_RESULT(env, node);
    }
  }

  XIL_ProcessResult(env, result);
}

void XIL_TranslateReference(struct XIL_TreeEnv *env, tree node)
{
  switch (TREE_CODE(node)) {

  case COMPONENT_REF: {
    tree structure = TREE_OPERAND(node, 0);
    XIL_Exp xil_structure = NULL;

    MAKE_ENV(structure_env, env->point, env->post_edges);
    structure_env.result_lval = &xil_structure;
    XIL_TranslateTree(&structure_env, structure);

    tree field = TREE_OPERAND(node, 1);
    XIL_Field xil_field = XIL_TranslateField(field);

    XIL_Exp lval_field = XIL_ExpFld(xil_structure, xil_field);
    XIL_Exp result = XIL_ExpDrf(lval_field);
    XIL_ProcessResult(env, result);
    return;
  }

  case INDIRECT_REF: {
    tree target = TREE_OPERAND(node, 0);
    XIL_Exp xil_target = NULL;

    MAKE_ENV(target_env, env->point, env->post_edges);
    target_env.result_rval = &xil_target;
    XIL_TranslateTree(&target_env, target);

    XIL_Exp result = XIL_ExpDrf(xil_target);
    XIL_ProcessResult(env, result);
    return;
  }

  case MEM_REF: {
    tree target = TREE_OPERAND(node, 0);
    XIL_Exp xil_target = NULL;

    tree constant = TREE_OPERAND(node, 1);
    if (TREE_UINT(constant) != 0)
      TREE_BOGUS_RESULT(env);

    MAKE_ENV(target_env, env->point, env->post_edges);
    target_env.result_rval = &xil_target;
    XIL_TranslateTree(&target_env, target);

    XIL_Exp result = XIL_ExpDrf(xil_target);
    XIL_ProcessResult(env, result);
    return;
  }

  case ARRAY_REF: {
    tree array = TREE_OPERAND(node, 0);
    XIL_Exp xil_array = NULL;

    MAKE_ENV(array_env, env->point, env->post_edges);
    array_env.result_lval = &xil_array;
    XIL_TranslateTree(&array_env, array);

    tree element_type = TREE_TYPE(node);
    XIL_Type xil_element_type = XIL_TranslateType(element_type);

    tree index = TREE_OPERAND(node, 1);
    XIL_Exp xil_index = NULL;

    MAKE_ENV(index_env, env->point, env->post_edges);
    index_env.result_rval = &xil_index;
    XIL_TranslateTree(&index_env, index);

    XIL_Exp access = XIL_ExpIndex(xil_array, xil_element_type, xil_index);
    XIL_Exp result = XIL_ExpDrf(access);
    XIL_ProcessResult(env, result);
    return;
  }

  case BIT_FIELD_REF: {
    // access some bits from a structure. this may have originated from
    // accessing a specific field in the original program, but if so that field
    // has not been preserved in the trees. punt on these before and just
    // get that field of the structure as a byte offset.
    tree structure = TREE_OPERAND(node, 0);
    tree bit_offset = TREE_OPERAND(node, 2);
    int byte_offset = TREE_UINT(bit_offset) / 8;

    XIL_Exp xil_structure = NULL;
    MAKE_ENV(structure_env, env->point, env->post_edges);
    structure_env.result_lval = &xil_structure;
    XIL_TranslateTree(&structure_env, structure);

    XIL_Exp xil_byte_offset = XIL_ExpInt(byte_offset);
    XIL_Type byte_type = XIL_TypeInt(1, 0);
    XIL_Exp result = XIL_ExpIndex(xil_structure, byte_type, xil_byte_offset);
    XIL_ProcessResult(env, result);
    return;
  }

  case VIEW_CONVERT_EXPR: {
    // this behaves like a type cast, just pass on the environment.
    tree operand = TREE_OPERAND(node, 0);
    XIL_TranslateTree(env, operand);
    return;
  }

  case REALPART_EXPR:
  case IMAGPART_EXPR:
    TREE_BOGUS_RESULT(env);

  default:
    TREE_UNEXPECTED_RESULT(env, node);
  }

  gcc_unreachable();
}

void XIL_TranslateComparison(struct XIL_TreeEnv *env, tree node)
{
  tree left = TREE_OPERAND(node, 0);
  tree right = TREE_OPERAND(node, 1);

  // check for a stride type for pointer comparisons.
  XIL_Type xil_stride_type = NULL;

  tree left_type = TREE_TYPE(left);
  if (TREE_CODE(left_type) == POINTER_TYPE) {
    tree stride_type = TREE_TYPE(left_type);
    xil_stride_type = XIL_TranslateType(stride_type);
  }

  XIL_BinopKind binop = 0;

  switch (TREE_CODE(node)) {
  case LT_EXPR: case UNLT_EXPR:
  case ORDERED_EXPR: case UNORDERED_EXPR:
    binop = xil_stride_type ? XIL_B_LessThanP : XIL_B_LessThan; break;
  case LE_EXPR: case UNLE_EXPR:
    binop = xil_stride_type ? XIL_B_LessEqualP : XIL_B_LessEqual; break;
  case GT_EXPR: case UNGT_EXPR:
    binop = xil_stride_type ? XIL_B_GreaterThanP : XIL_B_GreaterThan; break;
  case GE_EXPR: case UNGE_EXPR:
    binop = xil_stride_type ? XIL_B_GreaterEqualP : XIL_B_GreaterEqual; break;
  case EQ_EXPR: case UNEQ_EXPR:
    binop = xil_stride_type ? XIL_B_EqualP : XIL_B_Equal; break;
  case NE_EXPR:
    binop = xil_stride_type ? XIL_B_NotEqualP : XIL_B_NotEqual; break;
  default:
    TREE_UNEXPECTED_RESULT(env, node);
  }

  XIL_Exp xil_left = NULL;
  XIL_Exp xil_right = NULL;

  MAKE_ENV(left_env, env->point, env->post_edges);
  left_env.result_rval = &xil_left;

  MAKE_ENV(right_env, env->point, env->post_edges);
  right_env.result_rval = &xil_right;

  XIL_TranslateTree(&left_env, left);
  XIL_TranslateTree(&right_env, right);

  XIL_Exp result = XIL_ExpBinop(binop, xil_left, xil_right,
                                xil_stride_type, 0, true);
  XIL_ProcessResult(env, result);
}

// if super represents a supertype at offset zero within type, return the value
// of node with the implicit field accesses to get from type to super.
XIL_Exp XIL_CoerceSuperType(struct XIL_TreeEnv *env,
                            tree type, tree super, tree node)
{
  if (TREE_CODE(type) != RECORD_TYPE || TREE_CODE(super) != RECORD_TYPE)
    return NULL;

  tree decl = TYPE_FIELDS(type);
  while (decl) {
    bool offset_zero;
    if (TREE_CODE(decl) == FIELD_DECL && XIL_IsBaseField(decl, &offset_zero)) {
      tree field_type = TREE_TYPE(decl);

      // check if type directly inherits from super.
      if (TYPE_FIELDS(field_type) == TYPE_FIELDS(super)) {
        XIL_Exp xil_node = NULL;
        MAKE_ENV(node_env, env->point, env->post_edges);
        node_env.result_rval = &xil_node;
        XIL_TranslateTree(&node_env, node);

        XIL_Field field = XIL_TranslateField(decl);
        return XIL_ExpFld(xil_node, field);
      }

      // check if type transitively inherits from super.
      XIL_Exp chain = XIL_CoerceSuperType(env, field_type, super, node);
      if (chain) {
        XIL_Field field = XIL_TranslateField(decl);
        return XIL_ExpFld(chain, field);
      }
    }

    decl = TREE_CHAIN(decl);
  }

  return NULL;
}

void XIL_TranslateUnary(struct XIL_TreeEnv *env, tree node)
{
  tree right = TREE_OPERAND(node, 0);

  // whether we will just pass on our environment to the operand, and ignore
  // the unary operation itself.
  bool pass_env = false;

  switch (TREE_CODE(node)) {

  case NOP_EXPR: {
    // widening coercion or type cast. watch for coercions to supertypes.
    tree type = TREE_TYPE(right); 
    tree super = TREE_TYPE(node);

    if (TREE_CODE(type) == POINTER_TYPE &&
        TREE_CODE(TREE_TYPE(type)) == RECORD_TYPE &&
        TREE_CODE(super) == POINTER_TYPE &&
        TREE_CODE(TREE_TYPE(super)) == RECORD_TYPE) {
      XIL_Exp result =
        XIL_CoerceSuperType(env, TREE_TYPE(type), TREE_TYPE(super), right);
      if (result) {
        XIL_ProcessResult(env, result);
        return;
      }
    }
    pass_env = true;
  }

  case FLOAT_EXPR:
  case FIX_TRUNC_EXPR:
    // coercions on floating point values. ignore.
  case NON_LVALUE_EXPR:
    pass_env = true;
  default:
    break;
  }

  // if the unop doesn't have its result used then just evaluate
  // the operand for side effects.
  if (!XIL_TreeResultUsed(env))
    pass_env = true;

  if (pass_env) {
    XIL_TranslateTree(env, right);
    return;
  }

  XIL_Exp xil_right = NULL;
  MAKE_ENV(right_env, env->point, env->post_edges);
  right_env.result_rval = &xil_right;
  XIL_TranslateTree(&right_env, right);

  // leave this as zero to treat as a nop.
  XIL_UnopKind unop = 0;

  switch (TREE_CODE(node)) {

  case CONVERT_EXPR:  unop = XIL_U_Coerce; break;
  case NEGATE_EXPR:   unop = XIL_U_Neg; break;
  case BIT_NOT_EXPR:  unop = XIL_U_BitwiseNot; break;

  case ABS_EXPR: {
    // model this as:
    // abs right => (right < 0) ? -right : right
    XIL_Location loc = XIL_TryUpdateLocation(*env->point, node);

    tree type = TREE_TYPE(node);
    XIL_Type xil_type = XIL_TranslateType(type);

    XIL_Var temp_var = XIL_NewTemporary(xil_type);
    XIL_Exp temp_exp = XIL_ExpVar(temp_var);

    XIL_PPoint true_point = XIL_CFGAddPoint(loc);
    XIL_PPoint false_point = XIL_CFGAddPoint(loc);
    XIL_PPoint join_point = XIL_CFGAddPoint(loc);

    XIL_Exp zero_exp = XIL_ExpInt(0);
    XIL_Exp lt_exp = XIL_ExpBinop(XIL_B_LessThan, xil_right, zero_exp,
                                  NULL, 0, true);
    XIL_Exp neg_exp = XIL_ExpUnop(XIL_U_Neg, xil_right, 0, true);

    XIL_CFGEdgeAssume(*env->point, true_point, lt_exp, true);
    XIL_CFGEdgeAssume(*env->point, false_point, lt_exp, false);
    XIL_CFGEdgeAssign(true_point, join_point, xil_type, temp_exp, neg_exp);
    XIL_CFGEdgeAssign(false_point, join_point, xil_type, temp_exp, xil_right);
    *env->point = join_point;

    XIL_Exp result = XIL_ExpDrf(temp_exp);
    XIL_ProcessResult(env, result);
    return;
  }

  default:
    TREE_UNEXPECTED_RESULT(env, node);
  }

  gcc_assert(unop);
  XIL_Exp result = XIL_ExpUnop(unop, xil_right, 0, true);
  XIL_ProcessResult(env, result);
}

// get the width in bytes to use for a pointer stride type.
int GetPointerStrideSize(tree type)
{
  tree unit_size = TYPE_SIZE_UNIT(type);
  if (unit_size)
    return TREE_UINT(unit_size);
  if (TREE_CODE(type) == VOID_TYPE)
    return 1;
  return 0;
}

void XIL_TranslateBinary(struct XIL_TreeEnv *env, tree node)
{
  tree left = TREE_OPERAND(node, 0);
  tree right = TREE_OPERAND(node, 1);

  XIL_Exp xil_left = NULL;
  XIL_Exp xil_right = NULL;

  MAKE_ENV(left_env, env->point, env->post_edges);
  left_env.result_rval = &xil_left;
  XIL_TranslateTree(&left_env, left);

  MAKE_ENV(right_env, env->point, env->post_edges);
  right_env.result_rval = &xil_right;
  XIL_TranslateTree(&right_env, right);

  // if one of the operands is a constant with its high bit set,
  // see if we want to treat that operand as a signed or unsigned value.
  // gcc doesn't always do what we'd like, e.g. x - 1 becomes x + 4294967295
  // if x is unsigned.

  tree type = TREE_TYPE(node);
  int bits = TYPE_SIZE(type) ?
    TREE_UINT(TYPE_SIZE(type)) : TYPE_PRECISION(type);

  switch (TREE_CODE(node)) {
  case PLUS_EXPR:
    xil_left = XIL_ExpSign(xil_left, bits, true);
    xil_right = XIL_ExpSign(xil_right, bits, true);
    break;

  case BIT_IOR_EXPR:
  case BIT_XOR_EXPR:
  case BIT_AND_EXPR:
    xil_left = XIL_ExpSign(xil_left, bits, false);
    xil_right = XIL_ExpSign(xil_right, bits, false);
    break;

  case POINTER_PLUS_EXPR:
    xil_right = XIL_ExpSign(xil_right, bits, true);
    break;

  default: break;
  }

  // if we can use a binop directly then do that.
  XIL_BinopKind binop = 0;

  switch (TREE_CODE(node)) {

  case PLUS_EXPR:    binop = XIL_B_Plus; break;
  case MULT_EXPR:    binop = XIL_B_Mult; break;
  case LSHIFT_EXPR:  binop = XIL_B_ShiftLeft; break;
  case RSHIFT_EXPR:  binop = XIL_B_ShiftRight; break;
  case BIT_IOR_EXPR: binop = XIL_B_BitwiseOr; break;
  case BIT_XOR_EXPR: binop = XIL_B_BitwiseXOr; break;
  case BIT_AND_EXPR: binop = XIL_B_BitwiseAnd; break;

  case TRUNC_DIV_EXPR:  binop = XIL_B_Div; break;
  case TRUNC_MOD_EXPR:  binop = XIL_B_Mod; break;
  case EXACT_DIV_EXPR:  binop = XIL_B_DivExact; break;

  case RDIV_EXPR: binop = XIL_B_Div; break;

  case MIN_EXPR: binop = XIL_B_Min; break;
  case MAX_EXPR: binop = XIL_B_Max; break;

  case POINTER_PLUS_EXPR: {
    tree type = TREE_TYPE(left);
    if (TREE_CODE(type) != POINTER_TYPE &&
        TREE_CODE(type) != REFERENCE_TYPE)
      TREE_UNEXPECTED_RESULT(env, node);
    tree stride_type = TREE_TYPE(type);
    XIL_Type xil_stride_type = XIL_TranslateType(stride_type);

    // pointer_plus changes the pointer in a measure of bytes, while we want
    // the change in terms of the stride type. insert a division, which we
    // should be able to simplify away in the resulting XIL_Exp.

    int bytes = GetPointerStrideSize(stride_type);
    if (!bytes) {
      xil_stride_type = XIL_TypeVoid();
      bytes = 1;
    }

    XIL_Exp bytes_exp = XIL_ExpInt(bytes);

    XIL_Exp divided = XIL_ExpBinop(XIL_B_DivExact, xil_right, bytes_exp,
                                   NULL, 0, true);
    XIL_Exp result = XIL_ExpBinop(XIL_B_PlusPI, xil_left, divided,
                                  xil_stride_type, 0, true);
    XIL_ProcessResult(env, result);
    return;
  }

  case MINUS_EXPR: {
    // there is no special POINTER_MINUS_EXPR, so figure out from the types
    // of the operands whether this is a pointer subtraction. if so then this
    // will be wrapped in an EXACT_DIV_EXPR which will cancel out the multiply
    // we insert here. we can just see 'pointer - pointer' here,
    // as 'pointer - index' will be converted to a POINTER_PLUS_EXPR.

    XIL_Type xil_stride_type = NULL;
    int bytes = 0;

    // the left/right sides will be coercions to an integer type.
    if (TREE_CODE(left) == CONVERT_EXPR &&
        TREE_CODE(right) == CONVERT_EXPR) {
      tree left_type = TREE_TYPE(TREE_OPERAND(left, 0));
      tree right_type = TREE_TYPE(TREE_OPERAND(right, 0));

      if (TREE_CODE(left_type) == POINTER_TYPE &&
          TREE_CODE(right_type) == POINTER_TYPE) {
        int left_bytes = GetPointerStrideSize(TREE_TYPE(left_type));
        int right_bytes = GetPointerStrideSize(TREE_TYPE(right_type));

        if (left_bytes == right_bytes) {
          xil_stride_type = XIL_TranslateType(TREE_TYPE(left_type));
          bytes = left_bytes;
        }

        if (!bytes) {
          xil_stride_type = XIL_TypeVoid();
          bytes = 1;
        }
      }
    }

    // for regular subractions just use B_Minus.
    if (!xil_stride_type) {
      binop = XIL_B_Minus;
      break;
    }

    XIL_Exp bytes_exp = XIL_ExpInt(bytes);
    XIL_Exp diff = XIL_ExpBinop(XIL_B_MinusPP, xil_left, xil_right,
                                xil_stride_type, 0, true);
    XIL_Exp result = XIL_ExpBinop(XIL_B_Mult, diff, bytes_exp, NULL, 0, true);
    XIL_ProcessResult(env, result);
    return;
  }

  case LROTATE_EXPR:
  case RROTATE_EXPR: {
    // model these as:
    // left lrotate right => (left << right) | (left >> (nbits - right)).
    // left rrotate right => (left >> right) | (left << (nbits - right)).

    tree type = TREE_TYPE(node);
    int nbits = TREE_UINT(TYPE_SIZE(type));
    XIL_Exp nbits_exp = XIL_ExpInt(nbits);

    XIL_BinopKind binop1 =
      (TREE_CODE(node) == LROTATE_EXPR) ? XIL_B_ShiftLeft : XIL_B_ShiftRight;
    XIL_BinopKind binop2 =
      (TREE_CODE(node) == LROTATE_EXPR) ? XIL_B_ShiftRight : XIL_B_ShiftLeft;

    XIL_Exp shift1 = XIL_ExpBinop(binop1, xil_left, xil_right,
                                  NULL, 0, true);
    XIL_Exp bits_diff = XIL_ExpBinop(XIL_B_Minus, nbits_exp, xil_right,
                                     NULL, 0, true);
    XIL_Exp shift2 = XIL_ExpBinop(binop2, xil_left, bits_diff,
                                  NULL, 0, true);

    XIL_Exp result = XIL_ExpBinop(XIL_B_BitwiseOr, shift1, shift2,
                                  NULL, 0, true);
    XIL_ProcessResult(env, result);
    return;
  }

  default:
    TREE_UNEXPECTED_RESULT(env, node);
  }

  gcc_assert(binop);
  XIL_Exp result = XIL_ExpBinop(binop, xil_left, xil_right, NULL, 0, true);
  XIL_ProcessResult(env, result);
}

static bool is_annotation_variable(const char *name)
{
  return !strcmp(name, "__initial") || !strcmp(name, "__gcsafe");
}

static XIL_Exp get_annotation_variable_value(const char *name, XIL_Exp base)
{
  if (!strcmp(name, "__initial"))
    return XIL_ExpInitial(base);
  if (!strcmp(name, "__gcsafe"))
    return XIL_ExpGCSafe(base);
  gcc_assert(false);
}

void XIL_TranslateStatement(struct XIL_TreeEnv *env, tree node)
{
  XIL_Location loc = XIL_TryUpdateLocation(*env->point, node);

  switch (TREE_CODE(node)) {

  case DECL_EXPR: {
    tree decl = DECL_EXPR_DECL(node);

    // skip 'using' declarations within a function.
    if (TREE_CODE(decl) == USING_DECL)
      return;

    // skip declarations we see while processing annotation files,
    // unless there is an explicit initializer.
    if (xil_has_annotation && !DECL_INITIAL(decl))
      return;

    // if there is an annotation hanging off this decl then process it.
    tree attr = DECL_ATTRIBUTES(decl);
    while (attr) {
      if (!*env->point)
        *env->point = XIL_CFGAddPoint(loc);
      if (XIL_ProcessAnnotationAttr(xil_active_env.decl, attr,
                                    env->point, loc))
        return;
      attr = TREE_CHAIN(attr);
    }

    XIL_Var var_decl = XIL_TranslateVar(decl);
    XIL_Exp exp_decl = XIL_ExpVar(var_decl);

    // get the local data for this decl. if there isn't any then the variable
    // is global (either an extern or static local) and its initializer will
    // be handled separately.
    struct XIL_LocalData *local = xil_active_env.locals;
    while (local) {
      if (local->decl == decl)
        break;
      local = local->block_next;
    }
    if (!local)
      return;

    // remember this declaration in the current scope. find the first scope
    // which is not a cleanup point (these aren't language scopes).
    struct XIL_ScopeEnv *scope = xil_active_scope;
    while (scope && scope->cleanup_edges)
      scope = scope->parent;
    gcc_assert(scope);
    local->scope_next = scope->locals;
    scope->locals = local;

    tree type = TREE_TYPE(decl);
    XIL_Type xil_type = XIL_TranslateType(type);

    // insert a call to alloca for variable sized arrays.
    if (TREE_CODE(type) == ARRAY_TYPE) {
      tree size = TYPE_SIZE_UNIT(type);
      if (size && TREE_CODE(size) != INTEGER_CST) {
        XIL_Exp xil_size = NULL;

        MAKE_ENV(size_env, env->point, NULL);
        size_env.result_rval = &xil_size;
        XIL_TranslateTree(&size_env, size);

        // get the signature for an allocation function: void* func(size_t);
        XIL_Type void_type = XIL_TypeVoid();
        XIL_Type void_ptr = XIL_TypePointer(void_type, xil_pointer_width);
        XIL_Type size_type = XIL_TypeInt(xil_pointer_width, 0);
        XIL_Type alloca_type =
          XIL_TypeFunction(void_ptr, NULL, 0, &size_type, 1);

        XIL_Var alloca_func = XIL_VarFunc("__xil_alloca", "__xil_alloca");
        XIL_Exp alloca_exp = XIL_ExpVar(alloca_func);

        XIL_PPoint after_point = XIL_CFGAddPoint(loc);
        XIL_CFGEdgeCall(*env->point, after_point,
                        alloca_type, exp_decl, NULL, alloca_exp, &xil_size, 1);
        *env->point = after_point;
      }
    }

    // do any initial value assignment.
    tree value = DECL_INITIAL(decl);
    if (!value)
      return;

    // check if this declaration annotates a special Initial or GCSafe expression.
    if (xil_has_annotation && DECL_NAME(decl)) {
      const char *name = IDENTIFIER_POINTER(DECL_NAME(decl));
      if (is_annotation_variable(name)) {
        XIL_Exp xil_value;
        MAKE_ENV(initial_env, env->point, env->post_edges);
        initial_env.result_lval = &xil_value;
        XIL_TranslateTree(&initial_env, value);

        XIL_PPoint after_point = XIL_CFGAddPoint(loc);
        XIL_Exp value = get_annotation_variable_value(name, xil_value);
        XIL_CFGEdgeAssign(*env->point, after_point,
                          xil_type, exp_decl, value);

        *env->point = after_point;
        return;
      }
    }

    MAKE_ENV(initial_env, env->point, env->post_edges);
    initial_env.result_assign = exp_decl;
    initial_env.result_assign_type = xil_type;

    XIL_TranslateTree(&initial_env, value);
    return;
  }

  case RETURN_EXPR: {
    tree operand = TREE_OPERAND(node, 0);

    if (operand) {
      MAKE_ENV(empty_env, env->point, NULL);
      XIL_TranslateTree(&empty_env, operand);
    }

    XIL_ResolveGoto(*env->point, xil_active_env.exit_point,
                    xil_active_scope, NULL);

    // code after the return is unreachable.
    *env->point = 0;
    return;
  }

  case LABEL_EXPR: {
    tree label_decl = TREE_OPERAND(node, 0);
    TREE_CHECK(label_decl, LABEL_DECL);

    struct XIL_LabelData **pdata =
      (struct XIL_LabelData**) XIL_Associate(XIL_AscBlock, "Label", label_decl);
    if (!*pdata)
      *pdata = xcalloc(1, sizeof(struct XIL_LabelData));
    struct XIL_LabelData *label_data = *pdata;

    // remember the point we were at when seeing this label. we need to
    // make a new point if the current environment's point is unreachable.
    gcc_assert(!label_data->point);
    if (*env->point == 0)
      *env->point = XIL_CFGAddPoint(loc);
    label_data->point = *env->point;
    label_data->scope = xil_active_scope;

    // resolve any gotos we previously saw but were not able to handle.
    while (label_data->gotos) {
      XIL_ResolveGoto(label_data->gotos->point, *env->point,
                      label_data->gotos->scope, xil_active_scope);
      XIL_CFGAddLoopHead(label_data->point, NULL);
      label_data->gotos = label_data->gotos->next;
    }

    return;
  }

  case GOTO_EXPR: {
    tree label_decl = TREE_OPERAND(node, 0);

    // don't handle computed gotos.
    if (TREE_CODE(label_decl) != LABEL_DECL)
      TREE_UNHANDLED_RESULT(env);

    struct XIL_LabelData **pdata =
      (struct XIL_LabelData**) XIL_Associate(XIL_AscBlock, "Label", label_decl);
    if (!*pdata)
      *pdata = xcalloc(1, sizeof(struct XIL_LabelData));
    struct XIL_LabelData *label_data = *pdata;

    if (label_data->point) {
      XIL_ResolveGoto(*env->point, label_data->point,
                      xil_active_scope, label_data->scope);
      XIL_CFGAddLoopHead(label_data->point, NULL);
    }
    else {
      // don't know the point or scope of the target, wait until
      // we see the label.
      struct XIL_GotoData *goto_data = xcalloc(1, sizeof(struct XIL_GotoData));
      goto_data->point = *env->point;
      goto_data->scope = xil_active_scope;
      goto_data->next = label_data->gotos;
      label_data->gotos = goto_data;
    }

    // code after the goto is unreachable.
    *env->point = 0;
    return;
  }

  case SWITCH_EXPR:
  case SWITCH_STMT: {
    tree test = TREE_OPERAND(node, 0);
    tree body = TREE_OPERAND(node, 1);

    if (!body)
      TREE_UNEXPECTED_RESULT(env, node);

    XIL_Exp xil_test = NULL;

    MAKE_ENV(test_env, env->point, NULL);
    test_env.result_rval = &xil_test;
    XIL_TranslateTree(&test_env, test);

    XIL_PPoint after_point = XIL_CFGAddPoint(loc);

    XIL_ActivePushScope();
    xil_active_scope->switch_test = xil_test;
    xil_active_scope->switch_point = *env->point;
    xil_active_scope->break_point = after_point;

    XIL_PPoint body_point = 0;
    MAKE_ENV(body_env, &body_point, NULL);
    XIL_TranslateTree(&body_env, body);

    // if we don't jump to any of the case labels, jump to the default label
    // if there is one, else the end of the switch.
    if (xil_active_scope->default_point) {
      XIL_CFGEdgeSkip(xil_active_scope->switch_point,
                      xil_active_scope->default_point);
    }
    else {
      if (!body_point)
        body_point = XIL_CFGAddPoint(loc);
      XIL_CFGEdgeSkip(xil_active_scope->switch_point, body_point);
    }

    XIL_CFGEdgeSkip(body_point, after_point);
    *env->point = after_point;
    XIL_ActivePopScope();
    return;
  }

  case CASE_LABEL_EXPR: {
    // find the innermost enclosing switch scope.
    struct XIL_ScopeEnv *scope = xil_active_scope;
    while (scope && !scope->switch_test)
      scope = scope->parent;
    if (!scope)
      TREE_UNEXPECTED_RESULT(env, node);

    // make a new point if the current point is unreachable.
    if (*env->point == 0)
      *env->point = XIL_CFGAddPoint(loc);

    tree case_low = CASE_LOW(node);
    tree case_high = CASE_HIGH(node);

    if (case_low) {
      XIL_Exp xil_case_low = NULL;
      MAKE_ENV(case_low_env, env->point, NULL);
      case_low_env.result_rval = &xil_case_low;
      XIL_TranslateTree(&case_low_env, case_low);

      // condition under which this case is taken.
      XIL_Exp test_binop = NULL;

      if (case_high) {
        // range case label.
        XIL_Exp xil_case_high = NULL;
        MAKE_ENV(case_high_env, env->point, NULL);
        case_high_env.result_rval = &xil_case_high;
        XIL_TranslateTree(&case_high_env, case_high);

        XIL_Exp ge_binop =
          XIL_ExpBinop(XIL_B_GreaterEqual, scope->switch_test, xil_case_low,
                       NULL, 0, true);
        XIL_Exp le_binop =
          XIL_ExpBinop(XIL_B_LessEqual, scope->switch_test, xil_case_high,
                       NULL, 0, true);
        test_binop =
          XIL_ExpBinop(XIL_B_LogicalAnd, ge_binop, le_binop, NULL, 0, true);
      }
      else {
        // regular case label.
        test_binop =
          XIL_ExpBinop(XIL_B_Equal, scope->switch_test, xil_case_low,
                       NULL, 0, true);
      }

      XIL_CFGEdgeAssume(scope->switch_point, *env->point, test_binop, true);

      XIL_PPoint after_point = XIL_CFGAddPoint(loc);
      XIL_CFGEdgeAssume(scope->switch_point, after_point, test_binop, false);
      scope->switch_point = after_point;
    }
    else {
      // default label.
      if (scope->default_point)
        TREE_UNEXPECTED_RESULT(env, node);
      else
        scope->default_point = *env->point;
    }

    return;
  }

  case ASM_EXPR: {
    XIL_PPoint after_point = XIL_CFGAddPoint(loc);
    XIL_CFGEdgeAssembly(*env->point, after_point);
    *env->point = after_point;
    return;
  }

  case CLEANUP_STMT: {
    tree body = TREE_OPERAND(node, 0);
    tree cleanup = TREE_OPERAND(node, 1);

    XIL_ActivePushScope();
    xil_active_scope->cleanup = cleanup;

    MAKE_ENV(body_env, env->point, NULL);
    XIL_TranslateTree(&body_env, body);

    XIL_ActivePopScope();

    MAKE_ENV(cleanup_env, env->point, NULL);
    XIL_TranslateTree(&cleanup_env, cleanup);
    return;
  }

  case EH_SPEC_BLOCK: {
    tree body = TREE_OPERAND(node, 0);
    MAKE_ENV(body_env, env->point, NULL);
    XIL_TranslateTree(&body_env, body);
    return;
  }

  case IF_STMT: {
    // these are the same as COND_EXPR from the perspective of the translator,
    // but fall in different buckets.
    void XIL_TranslateExpression(struct XIL_TreeEnv *env, tree node);
    XIL_TranslateExpression(env, node);
    return;
  }

  case WHILE_STMT: {
    tree cond = TREE_OPERAND(node, 0);
    tree body = TREE_OPERAND(node, 1);

    // as with labels, always consider the entry points of loops to be
    // reachable. even if there is no control path directly to the head of
    // the loop, there may be a jump into the middle of the loop.
    if (*env->point == 0)
      *env->point = XIL_CFGAddPoint(loc);

    XIL_PPoint start_point = *env->point;
    XIL_PPoint after_point = XIL_CFGAddPoint(loc);
    XIL_PPoint body_point = XIL_CFGAddPoint(loc);
    XIL_CFGAddLoopHead(start_point, NULL);

    XIL_ActivePushScope();
    xil_active_scope->continue_point = start_point;
    xil_active_scope->break_point = after_point;

    MAKE_ENV(cond_env, env->point, NULL);
    cond_env.result_branch = true;
    cond_env.true_point = body_point;
    cond_env.false_point = after_point;
    XIL_TranslateTree(&cond_env, cond);

    MAKE_ENV(body_env, &body_point, NULL);
    XIL_TranslateTree(&body_env, body);

    XIL_CFGEdgeSkip(body_point, start_point);
    XIL_ActivePopScope();

    *env->point = after_point;
    return;
  }

  case DO_STMT: {
    tree cond = TREE_OPERAND(node, 0);
    tree body = TREE_OPERAND(node, 1);

    if (*env->point == 0)
      *env->point = XIL_CFGAddPoint(loc);

    XIL_PPoint start_point = *env->point;
    XIL_PPoint after_point = XIL_CFGAddPoint(loc);
    XIL_CFGAddLoopHead(start_point, NULL);

    XIL_ActivePushScope();
    xil_active_scope->continue_point = start_point;
    xil_active_scope->break_point = after_point;

    MAKE_ENV(body_env, env->point, NULL);
    XIL_TranslateTree(&body_env, body);

    MAKE_ENV(cond_env, env->point, NULL);
    cond_env.result_branch = true;
    cond_env.true_point = start_point;
    cond_env.false_point = after_point;
    XIL_TranslateTree(&cond_env, cond);

    XIL_ActivePopScope();

    *env->point = after_point;
    return;
  }

  case FOR_STMT: {
    tree init = TREE_OPERAND(node, 0);
    tree cond = TREE_OPERAND(node, 1);
    tree expr = TREE_OPERAND(node, 2);
    tree body = TREE_OPERAND(node, 3);

    if (init) {
      // this doesn't seem to actually be used.
      TREE_UNEXPECTED_RESULT(env, node);
    }

    if (*env->point == 0)
      *env->point = XIL_CFGAddPoint(loc);

    XIL_PPoint start_point = *env->point;
    XIL_PPoint after_point = XIL_CFGAddPoint(loc);
    XIL_PPoint body_point = XIL_CFGAddPoint(loc);
    XIL_PPoint expr_point = XIL_CFGAddPoint(loc);
    XIL_CFGAddLoopHead(start_point, NULL);

    XIL_ActivePushScope();
    xil_active_scope->continue_point = expr_point;
    xil_active_scope->break_point = after_point;

    if (cond) {
      MAKE_ENV(cond_env, env->point, NULL);
      cond_env.result_branch = true;
      cond_env.true_point = body_point;
      cond_env.false_point = after_point;
      XIL_TranslateTree(&cond_env, cond);
    }
    else {
      XIL_CFGEdgeSkip(*env->point, body_point);
    }

    gcc_assert(body);
    MAKE_ENV(body_env, &body_point, NULL);
    XIL_TranslateTree(&body_env, body);

    XIL_CFGEdgeSkip(body_point, expr_point);

    if (expr) {
      MAKE_ENV(expr_env, &expr_point, NULL);
      XIL_TranslateTree(&expr_env, expr);
    }

    XIL_CFGEdgeSkip(expr_point, start_point);
    XIL_ActivePopScope();

    *env->point = after_point;
    return;
  }

  case BREAK_STMT: {
    struct XIL_ScopeEnv *scope = xil_active_scope;
    while (scope) {
      if (scope->break_point) break;
      scope = scope->parent;
    }
    if (!scope) TREE_UNEXPECTED_RESULT(env, node);

    XIL_ResolveGoto(*env->point, scope->break_point,
                    xil_active_scope, scope);

    // code after the break is unreachable.
    *env->point = 0;
    return;
  }

  case CONTINUE_STMT: {
    struct XIL_ScopeEnv *scope = xil_active_scope;
    while (scope) {
      if (scope->continue_point) break;
      scope = scope->parent;
    }
    if (!scope) TREE_UNEXPECTED_RESULT(env, node);

    XIL_ResolveGoto(*env->point, scope->continue_point,
                    xil_active_scope, scope);

    // code after the continue is unreachable.
    *env->point = 0;
    return;
  }

  case TRY_CATCH_EXPR:
  case TRY_BLOCK: {
    tree body = TREE_OPERAND(node, 0);
    if (body)
      XIL_TranslateTree(env, body);
    return;
  }

  case LOOP_EXPR: {
    tree body = TREE_OPERAND(node, 0);

    XIL_PPoint start_point = *env->point;
    XIL_PPoint after_point = XIL_CFGAddPoint(loc);
    XIL_CFGAddLoopHead(start_point, NULL);

    XIL_ActivePushScope();
    xil_active_scope->exit_point = after_point;

    MAKE_ENV(body_env, env->point, NULL);
    XIL_TranslateTree(&body_env, body);

    XIL_CFGEdgeSkip(*env->point, start_point);
    XIL_ActivePopScope();

    *env->point = after_point;
    return;
  }

  case EXIT_EXPR: {
    tree cond = TREE_OPERAND(node, 0);

    struct XIL_ScopeEnv *scope = xil_active_scope;
    while (scope) {
      if (scope->exit_point) break;
      scope = scope->parent;
    }
    if (!scope) TREE_UNEXPECTED_RESULT(env, node);

    XIL_PPoint next_point = XIL_CFGAddPoint(loc);

    MAKE_ENV(cond_env, env->point, NULL);
    cond_env.result_branch = true;
    cond_env.true_point = scope->exit_point;
    cond_env.false_point = next_point;
    XIL_TranslateTree(&cond_env, cond);

    *env->point = next_point;
    return;
  }

  case USING_STMT:
    // these show up with 'using' directives inside a function. ignore.
    return;

  default:
    TREE_UNEXPECTED_RESULT(env, node);
  }

  gcc_unreachable();
}

// if we are in an annotation and node is a call to a special annotation
// function, generate the corresponding analysis expression for env
// and return true.
bool XIL_TranslateAnnotationCall(struct XIL_TreeEnv *env, tree node)
{
  // annotation calls can only appear in annotations.
  if (!xil_has_annotation) return false;

  tree function = TREE_OPERAND(node, 1);
  if (TREE_CODE(function) != ADDR_EXPR) return false;

  tree function_var = TREE_OPERAND(function, 0);
  if (TREE_CODE(function_var) != FUNCTION_DECL) return false;

  tree function_name = DECL_NAME(function_var);
  if (!function_name || TREE_CODE(function_name) != IDENTIFIER_NODE)
    return false;
  const char *name = IDENTIFIER_POINTER(function_name);

  if (!strcmp(name, "skip_inference")) {
    XIL_Exp result = XIL_ExpSkipInference();
    XIL_ProcessResult(env, result);
    return true;
  }

  if (strcmp(name,"__ubound") && strcmp(name,"__lbound") &&
      strcmp(name,"__zterm"))
    return false;

  // this is an annotation function call. get the argument being passed.
  tree arg = TREE_OPERAND(node, 3);
  if (!arg) return false;

  XIL_Exp xil_arg = NULL;
  MAKE_ENV(arg_env, env->point, NULL);
  arg_env.result_rval = &xil_arg;
  XIL_TranslateTree(&arg_env, arg);

  // figure out the stride type to use for this bound.

  tree type = TREE_TYPE(arg);
  if (TREE_CODE(type) != POINTER_TYPE) return false;

  XIL_Type stride_type = XIL_TranslateType(TREE_TYPE(type));

  XIL_Exp result = NULL;
  if (!strcmp(name,"__ubound"))
    result = XIL_ExpUBound(xil_arg, stride_type);
  else if (!strcmp(name,"__lbound"))
    result = XIL_ExpLBound(xil_arg, stride_type);
  else if (!strcmp(name,"__zterm"))
    result = XIL_ExpZTerm(xil_arg, stride_type);
  else
    gcc_unreachable();

  XIL_ProcessResult(env, result);
  return true;
}

// get the virtual function field for an obj_type_ref on a type.
static XIL_Field XIL_GetVTableField(tree type, tree node)
{
  static XIL_Field error_field = NULL;
  if (!error_field)
    error_field = XIL_MakeField("error", "error", "error", XIL_TypeError(), 0);

  TREE_CHECK(node, OBJ_TYPE_REF);

  // get the vtable index we'll use to determine the function field.
  int vtable_index = 0;

  tree walker = TREE_OPERAND(node, 0);
  if (TREE_CODE(walker) != INDIRECT_REF) {
    TREE_UNEXPECTED(node);
    return error_field;
  }
  walker = TREE_OPERAND(walker, 0);
  if (TREE_CODE(walker) == NON_LVALUE_EXPR)
    walker = TREE_OPERAND(walker, 0);

  if (TREE_CODE(walker) == POINTER_PLUS_EXPR) {
    // non-zero offset into the vtable. the amount we are adding
    // by should be a multiple of the pointer width.
    tree offset = TREE_OPERAND(walker, 1);
    walker = TREE_OPERAND(walker, 0);
    if (TREE_CODE(offset) != INTEGER_CST) {
      TREE_UNEXPECTED(node);
      return error_field;
    }
    vtable_index = TREE_UINT(offset) / xil_pointer_width;
    if (vtable_index * xil_pointer_width != TREE_UINT(offset)) {
      TREE_UNEXPECTED(node);
      return error_field;
    }
  }

  // find the original function field this vtable index corresponds to.
  struct XIL_VirtualFunction *virt = XIL_GetFunctionFields(type);

  for (; virt; virt = virt->next) {
    if (virt->index == vtable_index)
      return virt->field;
  }

  TREE_UNEXPECTED(node);
  return error_field;
}

void XIL_TranslateExpression(struct XIL_TreeEnv *env, tree node)
{
  XIL_Location loc = XIL_TryUpdateLocation(*env->point, node);

  switch (TREE_CODE(node)) {

  case BIND_EXPR: {
    // ignore the declared variables, we will see them later.
    XIL_TranslateTree(env, BIND_EXPR_BODY(node));
    return;
  }

  case COMPOUND_EXPR: {
    tree first = TREE_OPERAND(node, 0);
    tree second = TREE_OPERAND(node, 1);

    MAKE_ENV(first_env, env->point, env->post_edges);
    XIL_TranslateTree(&first_env, first);

    XIL_TranslateTree(env, second);
    return;
  }

  case COMPOUND_LITERAL_EXPR: {
    tree decl_expr = TREE_OPERAND(node, 0);
    TREE_CHECK(decl_expr, DECL_EXPR);

    // evaluate the DECL_EXPR to initialize the declared variable.
    MAKE_ENV(decl_env, env->point, NULL);
    XIL_TranslateTree(&decl_env, decl_expr);

    tree decl = DECL_EXPR_DECL(decl_expr);
    XIL_Var xil_var = XIL_TranslateVar(decl);
    XIL_Exp xil_exp = XIL_ExpVar(xil_var);
    XIL_Exp result = XIL_ExpDrf(xil_exp);
    XIL_ProcessResult(env, result);
    return;
  }

  // Default initialization for member arrays?
  case VEC_INIT_EXPR:
    TREE_BOGUS_RESULT(env);

  case SAVE_EXPR: {
    // associate each saved expression with the translation result,
    // excluding all side effects of the expression.
    XIL_Exp *saved_exp =
      (XIL_Exp*) XIL_Associate(XIL_AscBlock, "SaveResult", node);

    if (*saved_exp) {
      // reuse the old result we created when we first saw this expression.
      // TODO: is it possible that the variables mentioned in the saved
      // expression can be clobbered between where the expr first and last
      // appears? would need to use temporaries in this case.
      XIL_ProcessResult(env, *saved_exp);
      return;
    }

    tree target = TREE_OPERAND(node, 0);
    XIL_Exp xil_target = NULL;

    MAKE_ENV(target_env, env->point, NULL);
    target_env.result_rval = &xil_target;
    XIL_TranslateTree(&target_env, target);

    *saved_exp = xil_target;
    XIL_ProcessResult(env, xil_target);
    return;
  }

  case ADDR_EXPR: {
    tree target = TREE_OPERAND(node, 0);
    XIL_Exp addr_target = NULL;

    // watch for address-of-label. treat these as NULL pointers.
    if (TREE_CODE(target) == LABEL_DECL) {
      addr_target = XIL_ExpInt(0);
    }
    else {
      MAKE_ENV(target_env, env->point, env->post_edges);
      target_env.result_lval = &addr_target;
      XIL_TranslateTree(&target_env, target);
    }

    XIL_ProcessResult(env, addr_target);
    return;
  }

  case MODIFY_EXPR:
  case INIT_EXPR: {
    tree left = TREE_OPERAND(node, 0);
    tree right = TREE_OPERAND(node, 1);

    // check if we are updating a temporary variable that is used in
    // a containing TARGET_EXPR.
    struct XIL_TreeEnv **temp_env =
      (struct XIL_TreeEnv**) XIL_Associate(XIL_AscBlock, "TargetVar", left);
    if (*temp_env) {
      bool *temp_result =
        (bool*) XIL_Associate(XIL_AscBlock, "TargetResult", left);

      if (*temp_result) {
        // generated multiple assignments for this env.
        TREE_UNEXPECTED_RESULT(env, node);
      }
      *temp_result = true;

      XIL_TranslateTree(*temp_env, right);
      return;
    }

    // ignore assignments through the vtable field of a type.
    if (TREE_CODE(left) == COMPONENT_REF) {
      tree left_field = TREE_OPERAND(left, 1);
      if (DECL_VIRTUAL_P(left_field))
        return;
    }

    tree type = TREE_TYPE(node);
    XIL_Type xil_type = XIL_TranslateType(type);

    XIL_Exp xil_left = NULL;

    // hang any post side effects after this modify, unless the result of the
    // modify will itself be used.
    MAKE_POST_EDGES(post_local);
    struct XIL_PostEdges *post_edges =
      XIL_TreeResultUsed(env) ? env->post_edges : &post_local;

    MAKE_ENV(left_env, env->point, post_edges);
    left_env.result_lval = &xil_left;
    XIL_TranslateTree(&left_env, left);

    // check if we are assigning to an annotation variable.
    bool processed = false;
    if (xil_has_annotation && TREE_CODE(left) == VAR_DECL) {
      const char *name = IDENTIFIER_POINTER(DECL_NAME(left));
      if (is_annotation_variable(name)) {
        XIL_Exp xil_value;
        MAKE_ENV(right_env, env->point, post_edges);
        right_env.result_lval = &xil_value;
        XIL_TranslateTree(&right_env, right);

        XIL_PPoint after_point = XIL_CFGAddPoint(loc);
        XIL_Exp value = get_annotation_variable_value(name, xil_value);
        XIL_CFGEdgeAssign(*env->point, after_point,
                          xil_type, xil_left, value);

        *env->point = after_point;
        processed = true;
      }
    }

    if (!processed) {
      // standard assignment otherwise.
      MAKE_ENV(right_env, env->point, post_edges);
      right_env.result_assign = xil_left;
      right_env.result_assign_type = xil_type;
      XIL_TranslateTree(&right_env, right);
    }

    XIL_ConnectPostPoint(env->point, post_local);

    XIL_Exp result = XIL_ExpDrf(xil_left);
    XIL_ProcessResult(env, result);
    return;
  }

  case TARGET_EXPR: {
    tree target = TREE_OPERAND(node, 0);
    tree initializer = TREE_OPERAND(node, 1);
    tree cleanup = TREE_OPERAND(node, 2);

    // we need to generate the temporary if the initializer's result needs
    // to be assigned, if we need the lvalue of the initializer, or if we
    // will call a constructor to generate the temporary.
    tree type = TREE_TYPE(initializer);
    if (TREE_CODE(type) != VOID_TYPE || env->result_lval ||
        (TREE_CODE(initializer) == AGGR_INIT_EXPR &&
         AGGR_INIT_VIA_CTOR_P(initializer))) {
      XIL_Exp xil_target = NULL;
      MAKE_ENV(target_env, env->point, NULL);
      target_env.result_lval = &xil_target;
      XIL_TranslateTree(&target_env, target);

      MAKE_ENV(initializer_env, env->point, NULL);
      if (TREE_CODE(type) != VOID_TYPE) {
        initializer_env.result_assign = xil_target;
        initializer_env.result_assign_type = XIL_TranslateType(type);
      }
      XIL_TranslateTree(&initializer_env, initializer);

      if (cleanup) {
        // the cleanup is performed at the first containing cleanup point.
        struct XIL_ScopeEnv *scope = xil_active_scope;
        while (scope) {
          if (scope->cleanup_edges) break;
          scope = scope->parent;
        }
        if (!scope) TREE_UNEXPECTED_RESULT(env, node);

        if (!scope->cleanup_edges->end_point) {
          XIL_PPoint new_point = XIL_CFGAddPoint(loc);
          scope->cleanup_edges->start_point = new_point;
          scope->cleanup_edges->end_point = new_point;
        }

        XIL_PPoint cleanup_point = scope->cleanup_edges->end_point;
        MAKE_ENV(cleanup_env, &cleanup_point, NULL);
        XIL_TranslateTree(&cleanup_env, cleanup);
        scope->cleanup_edges->end_point = cleanup_point;
      }

      XIL_Exp result = XIL_ExpDrf(xil_target);
      XIL_ProcessResult(env, result);
      return;
    }

    // otherwise the only case we are handling is where the variable being
    // initialized is a dummy temporary, and the initializer does any writing
    // necessary to generate the result. instead of making our own temporary,
    // associate our environment with the variable and process the modify_exprs
    // on the variable as updates to our environment. we can ignore the cleanup
    // in this case as we are not generating the temporary.

    if (TREE_CODE(target) != VAR_DECL)
      TREE_UNEXPECTED_RESULT(env, node);

    if (DECL_NAME(target) != NULL)
      TREE_UNEXPECTED_RESULT(env, node);

    // add the association. we will pick this up at MODIFY_EXPR.
    struct XIL_TreeEnv **temp_env =
      (struct XIL_TreeEnv**) XIL_Associate(XIL_AscBlock, "TargetVar", target);
    if (*temp_env) TREE_UNEXPECTED_RESULT(env, node);
    *temp_env = env;

    MAKE_ENV(initializer_env, env->point, NULL);
    XIL_TranslateTree(&initializer_env, initializer);

    // make sure we generated an assignment to the temporary.
    bool *temp_result =
      (bool*) XIL_Associate(XIL_AscBlock, "TargetResult", target);
    if (!*temp_result) TREE_UNEXPECTED_RESULT(env, node);

    env->processed = true;
    return;
  }

  case TRUTH_ANDIF_EXPR:
  case TRUTH_ORIF_EXPR: {
    // treat this as a branch case regardless of the operation we need to do.
    tree left = TREE_OPERAND(node, 0);
    tree right = TREE_OPERAND(node, 1);

    XIL_Location loc = XIL_TryUpdateLocation(*env->point, node);
    bool is_and = (TREE_CODE(node) == TRUTH_ANDIF_EXPR);

    XIL_PPoint true_point = env->true_point;
    XIL_PPoint false_point = env->false_point;
    XIL_PPoint join_point = 0;

    XIL_PPoint mid_point = XIL_CFGAddPoint(loc);

    if (!true_point && !false_point) {
      true_point = XIL_CFGAddPoint(loc);
      false_point = XIL_CFGAddPoint(loc);
      join_point = XIL_CFGAddPoint(loc);
    }

    if (env->result_lval)
      TREE_UNEXPECTED_RESULT(env, node);

    if (env->result_assign || env->result_rval) {
      // transform this into a branch which assigns to a temporary on the
      // true/false results.

      XIL_Exp xil_lval = env->result_assign;
      XIL_Type xil_type = env->result_assign_type;
      if (env->result_rval) {
        tree type = TREE_TYPE(node);
        xil_type = XIL_TranslateType(type);
        xil_lval = XIL_ExpVar(XIL_NewTemporary(xil_type));
        *env->result_rval = XIL_ExpDrf(xil_lval);
      }

      XIL_Exp one_exp = XIL_ExpInt(1);
      XIL_Exp zero_exp = XIL_ExpInt(0);
      XIL_CFGEdgeAssign(true_point, join_point, xil_type, xil_lval, one_exp);
      XIL_CFGEdgeAssign(false_point, join_point, xil_type, xil_lval, zero_exp);
    }
    else if (join_point) {
      // result of the and/if not actually used.
      gcc_assert(!XIL_TreeResultUsed(env));
      XIL_CFGEdgeSkip(true_point, join_point);
      XIL_CFGEdgeSkip(false_point, join_point);
    }

    MAKE_ENV(left_env, env->point, NULL);
    left_env.result_branch = true;
    left_env.true_point = is_and ? mid_point : true_point;
    left_env.false_point = is_and ? false_point : mid_point;
    XIL_TranslateTree(&left_env, left);

    MAKE_ENV(right_env, &mid_point, NULL);
    right_env.result_branch = true;
    right_env.true_point = true_point;
    right_env.false_point = false_point;
    XIL_TranslateTree(&right_env, right);

    if (join_point)
      *env->point = join_point;
    else
      *env->point = 0;

    env->processed = true;
    return;
  }

  case TRUTH_AND_EXPR:
  case TRUTH_OR_EXPR:
  case TRUTH_XOR_EXPR: {
    tree left = TREE_OPERAND(node, 0);
    tree right = TREE_OPERAND(node, 1);

    XIL_Exp xil_left = NULL;
    XIL_Exp xil_right = NULL;

    MAKE_ENV(left_env, env->point, env->post_edges);
    left_env.result_rval = &xil_left;
    XIL_TranslateTree(&left_env, left);

    MAKE_ENV(right_env, env->point, env->post_edges);
    right_env.result_rval = &xil_right;
    XIL_TranslateTree(&right_env, right);

    XIL_BinopKind binop = 0;
    switch (TREE_CODE(node)) {
    case TRUTH_AND_EXPR: binop = XIL_B_LogicalAnd; break;
    case TRUTH_OR_EXPR: binop = XIL_B_LogicalOr; break;
    case TRUTH_XOR_EXPR: binop = XIL_B_NotEqual; break;
    default: gcc_unreachable();
    }

    XIL_Exp result = XIL_ExpBinop(binop, xil_left, xil_right,
                                  NULL, 0, true);
    XIL_ProcessResult(env, result);
    return;
  }

  case TRUTH_NOT_EXPR: {
    tree right = TREE_OPERAND(node, 0);

    XIL_Exp xil_right = NULL;
    MAKE_ENV(right_env, env->point, env->post_edges);
    right_env.result_rval = &xil_right;
    XIL_TranslateTree(&right_env, right);

    XIL_Exp result = XIL_ExpUnop(XIL_U_LogicalNot, xil_right, 0, true);
    XIL_ProcessResult(env, result);
    return;
  }

  case PREDECREMENT_EXPR:
  case PREINCREMENT_EXPR:
  case POSTDECREMENT_EXPR:
  case POSTINCREMENT_EXPR: {
    bool is_increment =
      (TREE_CODE(node) == PREINCREMENT_EXPR ||
       TREE_CODE(node) == POSTINCREMENT_EXPR);

    bool is_pre =
      (TREE_CODE(node) == PREINCREMENT_EXPR ||
       TREE_CODE(node) == PREDECREMENT_EXPR);

    // convert postincr/postdecr to preincr/predecr if the result of the
    // operation will not be used.
    if (!XIL_TreeResultUsed(env))
      is_pre = true;

    tree type = TREE_TYPE(node);
    XIL_Type xil_type = XIL_TranslateType(type);

    // stride type for pointer inc/dec.
    XIL_Type xil_stride_type = NULL;
    if (TREE_CODE(type) == POINTER_TYPE) {
      tree stride_type = TREE_TYPE(type);
      xil_stride_type = XIL_TranslateType(stride_type);
    }

    tree target = TREE_OPERAND(node, 0);
    XIL_Exp xil_target = NULL;

    MAKE_ENV(target_env, env->point, env->post_edges);
    target_env.result_lval = &xil_target;
    XIL_TranslateTree(&target_env, target);

    XIL_Exp drf_target = XIL_ExpDrf(xil_target);

    // the result of this expression is the deref of the updated lvalue,
    // except when we are doing a postincr/postdecr and don't have a later
    // place to hang the side effect. in this case introduce a temporary.
    XIL_Exp result = drf_target;

    if (!is_pre && !env->post_edges) {
      XIL_Var temp_var = XIL_NewTemporary(xil_type);
      XIL_Exp temp_lval = XIL_ExpVar(temp_var);
      result = XIL_ExpDrf(temp_lval);

      XIL_PPoint temp_point = XIL_CFGAddPoint(loc);
      XIL_CFGEdgeAssign(*env->point, temp_point,
                        xil_type, temp_lval, drf_target);
      *env->point = temp_point;
    }

    XIL_BinopKind binop = 0;
    if (is_increment)
      binop = xil_stride_type ? XIL_B_PlusPI : XIL_B_Plus;
    else
      binop = xil_stride_type ? XIL_B_MinusPI : XIL_B_Minus;

    XIL_Exp xil_one = XIL_ExpInt(1);
    XIL_Exp rhs_value = XIL_ExpBinop(binop, drf_target, xil_one,
                                     xil_stride_type, 0, true);

    // point for after the increment operation.
    XIL_PPoint after_point = XIL_CFGAddPoint(loc);

    // this goes either at the current environment point or the post side
    // effects, depending on the type of operation.
    if (is_pre || !env->post_edges) {
      XIL_CFGEdgeAssign(*env->point, after_point,
                        xil_type, xil_target, rhs_value);
      *env->point = after_point;
    }
    else {
      if (!env->post_edges->end_point) {
        // first post side effect we've seen for these edges, make a start
        // point for them.
        XIL_PPoint new_point = XIL_CFGAddPoint(loc);
        env->post_edges->start_point = new_point;
        env->post_edges->end_point = new_point;
      }

      XIL_CFGEdgeAssign(env->post_edges->end_point, after_point,
                        xil_type, xil_target, rhs_value);
      env->post_edges->end_point = after_point;
    }

    XIL_ProcessResult(env, result);
    return;
  }

  case COND_EXPR:
  case IF_STMT: {
    tree condition = TREE_OPERAND(node, 0);
    tree true_branch = TREE_OPERAND(node, 1);
    tree false_branch = TREE_OPERAND(node, 2);

    if (!condition || !true_branch)
      TREE_UNEXPECTED_RESULT(env, node);

    // NULL false branch is OK for if's without else's.
    if (!false_branch) {
      if (XIL_TreeResultUsed(env))
        TREE_UNEXPECTED_RESULT(env, node);
    }

    // not handling this case yet. is this possible?  &(a ? b : c)
    if (env->result_lval)
      TREE_UNEXPECTED_RESULT(env, node);

    // branch to new true/false points according to the condition value.
    MAKE_ENV(condition_env, env->point, NULL);
    condition_env.result_branch = true;
    condition_env.true_point = XIL_CFGAddPoint(loc);
    condition_env.false_point = XIL_CFGAddPoint(loc);
    XIL_TranslateTree(&condition_env, condition);

    MAKE_ENV(true_env, &condition_env.true_point, NULL);
    MAKE_ENV(false_env, &condition_env.false_point, NULL);

    if (env->result_branch) {
      true_env.result_branch = false_env.result_branch = true;
      true_env.true_point = false_env.true_point = env->true_point;
      true_env.false_point = false_env.false_point = env->false_point;
    }
    else if (env->result_assign) {
      true_env.result_assign = false_env.result_assign = env->result_assign;
      true_env.result_assign_type = false_env.result_assign_type =
        env->result_assign_type;
    }
    else if (env->result_rval) {
      tree type = TREE_TYPE(node);
      XIL_Type xil_type = XIL_TranslateType(type);

      XIL_Var temp_var = XIL_NewTemporary(xil_type);
      XIL_Exp temp_lval = XIL_ExpVar(temp_var);
      *env->result_rval = XIL_ExpDrf(temp_lval);

      true_env.result_assign = false_env.result_assign = temp_lval;
      true_env.result_assign_type = false_env.result_assign_type = xil_type;
    }

    XIL_TranslateTree(&true_env, true_branch);

    if (false_branch)
      XIL_TranslateTree(&false_env, false_branch);

    // if the two branches have fall throughs then make a join point.
    if (condition_env.true_point || condition_env.false_point) {
      XIL_PPoint join_point = XIL_CFGAddPoint(loc);
      XIL_CFGEdgeSkip(condition_env.true_point, join_point);
      XIL_CFGEdgeSkip(condition_env.false_point, join_point);
      *env->point = join_point;
    }
    else {
      // no fall through from this condition.
      *env->point = 0;
    }

    // we've already done all processing on the env.
    env->processed = true;
    return;
  }

  case CALL_EXPR:
  case AGGR_INIT_EXPR: {
    // check for special annotation functions being called.
    if (XIL_TranslateAnnotationCall(env, node))
      return;

    tree function = TREE_OPERAND(node, 1);

    // get the signature of the function. the function expression should be
    // of function pointer type.
    tree function_ptr_type = TREE_TYPE(function);
    if (TREE_CODE(function_ptr_type) != POINTER_TYPE)
      TREE_UNEXPECTED_RESULT(env, node);
    tree function_type = TREE_TYPE(function_ptr_type);
    if (TREE_CODE(function_type) != FUNCTION_TYPE &&
        TREE_CODE(function_type) != METHOD_TYPE)
      TREE_UNEXPECTED_RESULT(env, node);
    XIL_Type xil_function_type = XIL_TranslateType(function_type);

    // lvalue to hold the call result, if there is one.
    XIL_Exp result_lval = NULL;

    // whether we're done processing the result after the call.
    bool result_done = false;

    // for methods, the object to invoke the method on.
    XIL_Exp instance_object = NULL;

    if (XIL_TreeResultUsed(env)) {
      if (env->result_assign) {
        if(TREE_CODE(node) == AGGR_INIT_EXPR &&
           AGGR_INIT_VIA_CTOR_P(node)) {
          // this case shows up with operator new; the result of the ctor
          // is supposed to get assigned somewhere. instead, invoke the ctor
          // on the target of the assign (the result of the memory allocation).
          instance_object = env->result_assign;
        }
        else {
          // store the call result directly into the lvalue our env needs.
          result_lval = env->result_assign;
        }
        result_done = true;
      }
      else {
        tree type = TREE_TYPE(node);
        XIL_Type xil_type = XIL_TranslateType(type);

        XIL_Var temp_var = XIL_NewTemporary(xil_type);
        result_lval = XIL_ExpVar(temp_var);
      }
    }

    int arg_start = 0;
    if (TREE_CODE(node) == CALL_EXPR) {
      arg_start = 3;
      // we are not translating calls to nested functions with chain arguments.
      if (TREE_OPERAND(node, 2))
        TREE_UNEXPECTED_RESULT(env, node);
    }
    else {
      // aggr_init calls may initialize either through a function's return
      // value or through a constructor call. the operand layout differs
      // between the two cases.
      if (AGGR_INIT_VIA_CTOR_P(node)) {
        arg_start = 2;
      }
      else {
        if (result_lval)
          TREE_UNEXPECTED_RESULT(env, node);

        // operand 2 is the return value.
        tree result = TREE_OPERAND(node, 2);

        // check if this return value is a temporary from a TARGET_EXPR.
        struct XIL_TreeEnv **temp_env = (struct XIL_TreeEnv**)
          XIL_Associate(XIL_AscBlock, "TargetVar", result);
        if (*temp_env &&
            ((*temp_env)->result_assign || !XIL_TreeResultUsed(*temp_env))) {
          bool *temp_result =
            (bool*) XIL_Associate(XIL_AscBlock, "TargetResult", result);
          if (*temp_result) TREE_UNEXPECTED_RESULT(env, node);
          *temp_result = true;
          result_lval = (*temp_env)->result_assign;
        }
        else {
          // assign to the result operand otherwise.
          MAKE_ENV(result_env, env->point, NULL);
          result_env.result_lval = &result_lval;
          XIL_TranslateTree(&result_env, result);
        }

        arg_start = 3;
      }
    }

    int ind = 0, arg_count = TREE_OPERAND_LENGTH(node) - arg_start;
    XIL_Exp *args = xmalloc(sizeof(XIL_Exp) * arg_count);

    for (; ind < arg_count; ind++) {
      tree arg = TREE_OPERAND(node, ind + arg_start);
      XIL_Exp xil_arg = NULL;

      MAKE_ENV(arg_env, env->point, NULL);
      arg_env.result_rval = &xil_arg;
      XIL_TranslateTree(&arg_env, arg);

      args[ind] = xil_arg;
    }

    XIL_Exp xil_function = NULL;

    // if the call's type is a method, the first arg is the instance object.
    // fixup the arguments we just constructed.
    if (TREE_CODE(function_type) == METHOD_TYPE) {
      gcc_assert(arg_count);

      if (!instance_object)
        instance_object = args[0];

      for (ind = 0; ind < arg_count - 1; ind++)
        args[ind] = args[ind + 1];
      arg_count--;

      if (TREE_CODE(function) == OBJ_TYPE_REF) {
        // virtual call. get the type of the instance object and figure out
        // which field is being invoked.
        tree ptr_type = TREE_TYPE(TREE_OPERAND(node, arg_start));
        XIL_Field field = XIL_GetVTableField(TREE_TYPE(ptr_type), function);
        XIL_Exp empty = XIL_ExpEmpty();
        XIL_Exp empty_fld = XIL_ExpFld(empty, field);
        xil_function = XIL_ExpDrf(empty_fld);
      }
      else if (TREE_CODE(function) == ADDR_EXPR) {
        // direct member call, no special treatment needed for the function.
        MAKE_ENV(function_env, env->point, NULL);
        function_env.result_rval = &xil_function;
        XIL_TranslateTree(&function_env, function);
      }
      else if (TREE_CODE(function) == COND_EXPR) {
        // COND_EXPR method calls seem to come up just with pointer-to-member.
        if (TREE_CODE(function) == COND_EXPR)
          TREE_BOGUS_RESULT(env);
      }
      else {
        // otherwise couldn't figure out the relation between the instance
        // object and the function pointer.
        TREE_BOGUS_RESULT(env);
      }
    }
    else {
      // direct or indirect call without an instance object.
      MAKE_ENV(function_env, env->point, NULL);
      function_env.result_rval = &xil_function;
      XIL_TranslateTree(&function_env, function);
    }

    XIL_PPoint after_point = XIL_CFGAddPoint(loc);

    XIL_CFGEdgeCall(*env->point, after_point, xil_function_type,
                    result_lval, instance_object, xil_function,
                    args, arg_count);
    *env->point = after_point;

    if (result_done) {
      env->processed = true;
      return;
    }

    if (!result_lval)
      return;

    XIL_Exp result_drf = XIL_ExpDrf(result_lval);
    XIL_ProcessResult(env, result_drf);
    return;
  }

  case PREDICT_EXPR: {
    // evaluate the operand for side effects.
    tree value = TREE_OPERAND(node, 0);
    MAKE_ENV(value_env, env->point, NULL);
    XIL_TranslateTree(&value_env, value);
    return;
  }

  case VA_ARG_EXPR: {
    // make a function call for these.
    tree list = TREE_OPERAND(node, 0);

    tree type = TREE_TYPE(node);
    XIL_Type xil_type = XIL_TranslateType(type);
    XIL_Type arg_type = XIL_TypePointer(XIL_TypeVoid(), xil_pointer_width);
    XIL_Type func_type = XIL_TypeFunction(xil_type, NULL, false, &arg_type, 1);

    XIL_Exp xil_list = NULL;
    MAKE_ENV(list_env, env->point, NULL);
    list_env.result_rval = &xil_list;
    XIL_TranslateTree(&list_env, list);

    XIL_Var func_var = XIL_VarFunc("va_arg", "va_arg");
    XIL_Exp func_exp = XIL_ExpVar(func_var);

    XIL_Var ret_var = XIL_NewTemporary(xil_type);
    XIL_Exp ret_lval = XIL_ExpVar(ret_var);

    XIL_PPoint after_point = XIL_CFGAddPoint(loc);
    XIL_CFGEdgeCall(*env->point, after_point,
                    func_type, ret_lval, NULL, func_exp, &xil_list, 1);
    *env->point = after_point;

    XIL_Exp result = XIL_ExpDrf(ret_lval);
    XIL_ProcessResult(env, result);
    return;
  }

  case CLEANUP_POINT_EXPR: {
    tree operand = TREE_OPERAND(node, 0);
    MAKE_POST_EDGES(cleanup_edges);

    XIL_ActivePushScope();
    xil_active_scope->cleanup_edges = &cleanup_edges;

    XIL_Exp result = NULL;
    MAKE_ENV(operand_env, env->point, &cleanup_edges);
    if (XIL_TreeResultUsed(env))
      operand_env.result_rval = &result;
    XIL_TranslateTree(&operand_env, operand);

    XIL_ActivePopScope();

    // if there was cleanup performed, thread it onto the current point.
    if (cleanup_edges.start_point) {
      XIL_CFGEdgeSkip(*env->point, cleanup_edges.start_point);
      *env->point = cleanup_edges.end_point;
    }

    if (XIL_TreeResultUsed(env))
      XIL_ProcessResult(env, result);
    return;
  }

  case EXPR_STMT: {
    tree operand = TREE_OPERAND(node, 0);

    MAKE_ENV(operand_env, env->point, NULL);
    XIL_TranslateTree(&operand_env, operand);

    return;
  }

  case EMPTY_CLASS_EXPR: {
    tree type = TREE_TYPE(node);
    XIL_Type xil_type = XIL_TranslateType(type);

    XIL_Var temp_var = XIL_NewTemporary(xil_type);
    XIL_Exp temp_exp = XIL_ExpVar(temp_var);

    XIL_Exp result = XIL_ExpDrf(temp_exp);
    XIL_ProcessResult(env, result);
    return;
  }

  default:
    TREE_UNEXPECTED_RESULT(env, node);
  }

  gcc_unreachable();
}

void generate_TranslateTree(struct XIL_TreeEnv *env, tree node)
{
  gcc_assert(node);

  switch (TREE_CODE_CLASS(TREE_CODE(node))) {

  case tcc_constant:
    XIL_TranslateConstant(env, node); break;

  case tcc_declaration:
    XIL_TranslateDeclaration(env, node); break;

  case tcc_reference:
    XIL_TranslateReference(env, node); break;

  case tcc_comparison:
    XIL_TranslateComparison(env, node); break;

  case tcc_unary:
    XIL_TranslateUnary(env, node); break;

  case tcc_binary:
    XIL_TranslateBinary(env, node); break;

  case tcc_statement:
    XIL_TranslateStatement(env, node); break;

  case tcc_vl_exp:
  case tcc_expression:
    XIL_TranslateExpression(env, node); break;

  default:
    switch (TREE_CODE(node)) {

    case STATEMENT_LIST: {
      tree_stmt_iterator iter = tsi_start(node);

      // push a new scope to get any variable declarations.
      XIL_ActivePushScope();

      while (!tsi_end_p(iter)) {
        tree stmt = tsi_stmt(iter);
        tsi_next(&iter);

        if (!tsi_end_p(iter) || !XIL_TreeResultUsed(env)) {
          MAKE_POST_EDGES(post_local);
          MAKE_ENV(empty_env, env->point, &post_local);
          XIL_TranslateTree(&empty_env, stmt);
          XIL_ConnectPostPoint(env->point, post_local);
        }
        else {
          XIL_TranslateTree(env, stmt);
        }
      }

      XIL_ActivePopScope();
      break;
    }

    case CONSTRUCTOR: {
      tree type = TREE_TYPE(node);
      int ind, nelts = CONSTRUCTOR_NELTS(node);

      // make a temporary unless the constructor will be used in an assign
      XIL_Exp xil_lval = NULL;
      XIL_Exp result = NULL;
      if (env->result_assign) {
        xil_lval = env->result_assign;
      }
      else {
        XIL_Type xil_type = XIL_TranslateType(type);
        XIL_Var temp_var = XIL_NewTemporary(xil_type);
        xil_lval = XIL_ExpVar(temp_var);
        result = XIL_ExpDrf(xil_lval);
      }

      for (ind = 0; ind < nelts; ind++) {
        tree index = CONSTRUCTOR_ELT(node, ind)->index;
        tree value = CONSTRUCTOR_ELT(node, ind)->value;

        if (!index || !value) {
          TREE_UNEXPECTED_RESULT(env, node);
          continue;
        }

        bool handled = false;

        if (TREE_CODE(index) == INTEGER_CST) {
          if (TREE_CODE(type) != ARRAY_TYPE)
            TREE_BOGUS_RESULT(env);

          tree element_type = TREE_TYPE(type);
          XIL_Type xil_element_type = XIL_TranslateType(element_type);

          XIL_Exp xil_index = NULL;
          MAKE_ENV(index_env, env->point, NULL);
          index_env.result_rval = &xil_index;
          XIL_TranslateTree(&index_env, index);

          XIL_Exp xil_lval_index =
            XIL_ExpIndex(xil_lval, xil_element_type, xil_index);

          MAKE_ENV(value_env, env->point, NULL);
          value_env.result_assign = xil_lval_index;
          value_env.result_assign_type = xil_element_type;
          XIL_TranslateTree(&value_env, value);

          handled = true;
        }

        if (TREE_CODE(index) == RANGE_EXPR) {
          if (TREE_CODE(type) != ARRAY_TYPE)
            TREE_UNEXPECTED_RESULT(env, node);
          tree min_value = TREE_OPERAND(index, 0);
          tree max_value = TREE_OPERAND(index, 1);
          if (TREE_CODE(min_value) != INTEGER_CST ||
              TREE_CODE(max_value) != INTEGER_CST)
            TREE_UNEXPECTED_RESULT(env, node);

          tree element_type = TREE_TYPE(type);
          XIL_Type xil_element_type = XIL_TranslateType(element_type);

          int ind, first = TREE_UINT(min_value), last = TREE_UINT(max_value);
          for (ind = first; ind < last; ind++) {
            XIL_Exp xil_index = XIL_ExpInt(ind);
            XIL_Exp xil_lval_index =
              XIL_ExpIndex(xil_lval, xil_element_type, xil_index);

            MAKE_ENV(value_env, env->point, NULL);
            value_env.result_assign = xil_lval_index;
            value_env.result_assign_type = xil_element_type;
            XIL_TranslateTree(&value_env, value);
          }

          handled = true;
        }

        if (TREE_CODE(index) == FIELD_DECL) {
          XIL_Field xil_field = XIL_TranslateField(index);
          XIL_Exp xil_lval_field = XIL_ExpFld(xil_lval, xil_field);

          tree field_type = TREE_TYPE(index);
          XIL_Type xil_field_type = XIL_TranslateType(field_type);

          MAKE_ENV(value_env, env->point, NULL);
          value_env.result_assign = xil_lval_field;
          value_env.result_assign_type = xil_field_type;
          XIL_TranslateTree(&value_env, value);

          handled = true;
        }

        if (!handled)
          TREE_UNEXPECTED_RESULT(env, index);
      }

      if (result)
        XIL_ProcessResult(env, result);
      else
        env->processed = true;
      break;
    }

    case ERROR_MARK: {
      // don't generate an unexpected/unhandled, gcc already reported this.
      XIL_Var error_var = XIL_VarGlob("error", "error");
      XIL_Exp error_exp = XIL_ExpVar(error_var);
      XIL_Exp error_drf = XIL_ExpDrf(error_exp);
      XIL_ProcessResult(env, error_drf);
      break;
    }

    default:
      TREE_UNEXPECTED_RESULT(env, node);
    }

    break;
  }

  // if the caller wanted us to process the result of this tree in any way,
  // make sure we did.
  if (XIL_TreeResultUsed(env)) {
    if (!env->processed)
      TREE_UNEXPECTED_RESULT(env, node);

    if (env->result_rval && !*env->result_rval)
      TREE_UNEXPECTED_RESULT(env, node);
  }
}
