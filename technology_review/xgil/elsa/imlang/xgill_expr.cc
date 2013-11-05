// xgill_expr.cc        see license.txt for copyright and terms of use
// translation of expressions for xgill frontend.

#include "xgill.h"
#include <stdconv.h>

Xgill::Buffer scratch_buf_one;
Xgill::Buffer scratch_buf_two;

// get a reference on the result of a binary operation on left_op and right_op
// with result type res_type. consumes references on left_op and right_op.
Xgill::Exp* ProcessBinop(Type *left_type, Type *right_type, Type *res_type,
                         BinaryOp binop, Xgill::Exp *left_op, Xgill::Exp *right_op)
{
  // right_type is NULL for incr/decr operations.
  Assert(left_type);
  Assert(res_type);

  // drop any references in case we haven't already.
  left_type = left_type->asRval();
  if (right_type)
    right_type = right_type->asRval();
  res_type = res_type->asRval();

  size_t bits;
  bool sign;
  GetTypeBits(res_type, &bits, &sign);

  Xgill::Type *stride_type = NULL;
  Xgill::BinopKind new_binop = Xgill::B_Invalid;
  switch (binop) {

  // plus can be either arithmetic or pointer + integer
  case BIN_PLUS:
    if (left_type->isPointer()) {
      stride_type = GetType(left_type->asPointerType()->atType);
      new_binop = Xgill::B_PlusPI;
    }
    else if (left_type->isArrayType()) {
      stride_type = GetType(left_type->asArrayType()->eltType);
      new_binop = Xgill::B_PlusPI;
    }
    else {
      new_binop = Xgill::B_Plus;
    }
    break;

  // minus can be either arithmetic, pointer - integer or pointer - pointer
  case BIN_MINUS:
    if (left_type->isPointer() || left_type->isArrayType()) {
      Type *elem_type = left_type->isPointer()
        ? left_type->asPointerType()->atType
        : left_type->asArrayType()->eltType;
      stride_type = GetType(elem_type);

      if (right_type) {
        if (right_type->isPointer() || right_type->isArrayType())
          new_binop = Xgill::B_MinusPP;
        else
          new_binop = Xgill::B_MinusPI;
      }
      else {
        new_binop = Xgill::B_MinusPI;
      }
    }
    else {
      new_binop = Xgill::B_Minus;
    }
    break;

  case BIN_EQUAL:      new_binop = Xgill::B_Equal; break;
  case BIN_NOTEQUAL:   new_binop = Xgill::B_NotEqual; break;
  case BIN_LESS:       new_binop = Xgill::B_LessThan; break;
  case BIN_GREATER:    new_binop = Xgill::B_GreaterThan; break;
  case BIN_LESSEQ:     new_binop = Xgill::B_LessEqual; break;
  case BIN_GREATEREQ:  new_binop = Xgill::B_GreaterEqual; break;

  case BIN_MULT:    new_binop = Xgill::B_Mult; break;
  case BIN_DIV:     new_binop = Xgill::B_Div; break;
  case BIN_MOD:     new_binop = Xgill::B_Mod; break;
  case BIN_LSHIFT:  new_binop = Xgill::B_ShiftLeft; break;
  case BIN_RSHIFT:  new_binop = Xgill::B_ShiftRight; break;
  case BIN_BITAND:  new_binop = Xgill::B_BitwiseAnd; break;
  case BIN_BITXOR:  new_binop = Xgill::B_BitwiseXOr; break;
  case BIN_BITOR:   new_binop = Xgill::B_BitwiseOr; break;

  // we should not see other binops here. this includes BIN_And and BIN_Or.
  default:
    cout << "ERROR: Unexpected binop: " << toString(binop) << endl;
    Assert(false);
  }

  if (Xgill::IsCompareBinop(new_binop)) {
    // add any pointer type information for comparisons.

    if (left_type->isPointer()) {
      stride_type = GetType(left_type->asPointerType()->atType);
      new_binop = Xgill::PointerBinop(new_binop);
    }
    else if (left_type->isArrayType()) {
      stride_type = GetType(left_type->asArrayType()->eltType);
      new_binop = Xgill::PointerBinop(new_binop);
    }
  }

  size_t res_bits = bits;
  bool res_sign = sign;

  // drop the bits for pointer, compare and bitwise binops,
  // these can't overflow.
  if (stride_type ||
      Xgill::IsCompareBinop(new_binop) ||
      Xgill::IsBitwiseBinop(new_binop)) {
    res_bits = 0;
    res_sign = true;
  }

  Xgill::Exp *res = Xgill::Exp::MakeBinop(new_binop, left_op, right_op,
                                          stride_type, res_bits, res_sign);

  if (Xgill::IsBitwiseBinop(new_binop) && sign) {
    // force result to signed.
    res = Xgill::Exp::MakeUnop(Xgill::U_Coerce, res, bits, sign);
  }

  return res;
}

// add an extra Drf() to exp if it is a reference type.
Xgill::Exp* ReferenceAddDrf(Type *type, Xgill::Exp *exp)
{
  if (type && type->isReference())
    return Xgill::Exp::MakeDrf(exp);
  else
    return exp;
}

// remove a Drf() from val if it is of array or function type
// (taking its address implicitly). this is only done if we are not already
// going to take the address of the expression according to expr_env.
Xgill::Exp* ArrayRemoveDrf(const ExprEnv &expr_env,
                           Type *type, Xgill::Exp *exp)
{
  if (expr_env.result_lval || expr_env.result_assign_address) {
    return exp;
  }
  else if (type && (type->isArrayType() || type->isFunctionType())) {
    // check for dynamically sized arrays. we keep the Drf() as these
    // are converted into pointers.
    if (type->isArrayType() &&
        type->asArrayType()->size == ArrayType::DYN_SIZE)
      return exp;

    Xgill::Exp *target = ExpDereference(exp);
    target->IncRef();
    exp->DecRef();
    return target;
  }
  else {
    return exp;
  }
}

// get an expression whose dereference is exp. if exp is a Drf() expression
// (i.e. it is the value of some lvalue), this just pops the Drf()
// as in ExpDereference. otherwise a new temporary will need to be created
// to hold the value, and its address returned. this should end up only
// being used for taking a const& of a non-constant value,
// e.g. 'const int &x = 3', in which case the target of the temporary address
// pointer won't be updated.
Xgill::Exp* GetValueReference(PPoint *pre_point,
                              Type *type, Xgill::Exp *exp)
{
  Assert(!type->isReference());

  if (Xgill::ExpDrf *nexp = exp->IfDrf()) {
    Xgill::Exp *target = nexp->GetTarget();

    target->IncRef();
    exp->DecRef();
    return target;
  }

  // make a temporary and assign it the value.

  Xgill::Type *temp_type = GetType(type);
  Xgill::Exp *temp_lval = GetNewTemporary(temp_type);

  // point for after the assignment.
  Xgill::Location *loc = benv->cfg->GetPointLocation(*pre_point);
  loc->IncRef();
  PPoint after_point = benv->cfg->AddPoint(loc);

  temp_type->IncRef();
  Xgill::PEdge *temp_edge =
    Xgill::PEdge::MakeAssign(*pre_point, after_point,
                             temp_type, temp_lval, exp);
  benv->cfg->AddEdge(temp_edge);

  *pre_point = after_point;

  // return the temporary's value.
  temp_lval->IncRef();
  return temp_lval;
}

// make a temporary for holding the result of an expression for expr_env.
// the value of the temporary is either the result itself or a pointer to the
// lval whose value is the result, per expr_env.ResultAddressNeeded().
Xgill::Exp* MakeResultTemporary(const ExprEnv &expr_env, Type *type)
{
  Xgill::Type *temp_type = GetType(type);
  if (expr_env.ResultAddressNeeded())
    temp_type = Xgill::Type::MakePointer(temp_type, POINTER_WIDTH);
  return GetNewTemporary(temp_type);
}

// get the value of a temporary created with MakeResultTemporary.
// consumes a reference on temp_lval.
Xgill::Exp* GetResultTemporaryValue(const ExprEnv &expr_env,
                                    Xgill::Exp *temp_lval)
{
  if (expr_env.ResultAddressNeeded()) {
    Xgill::Exp *temp_drf = Xgill::Exp::MakeDrf(temp_lval);
    return Xgill::Exp::MakeDrf(temp_drf);
  }
  else {
    return Xgill::Exp::MakeDrf(temp_lval);
  }
}

void DoCallArguments(PPoint *pre_point,
                     FunctionType *type,
                     FakeList<ArgExpression> *call_args,
                     Xgill::Vector<Xgill::Exp*> *arguments)
{
  int arg_ind = 0;

  if (type && type->isMethod()) {
    // the first argument of method function types is the receiver class.
    arg_ind++;
  }

  while (call_args != NULL) {
    ArgExpression *arg = call_args->first();
    call_args = call_args->butFirst();

    // get the corresponding argument type, if available.
    Type *arg_type = NULL;
    if (type && arg_ind < type->params.count())
      arg_type = type->params.nth(arg_ind)->type;

    Xgill::Exp *arg_value;
    ExprEnv arg_expr_env(pre_point);

    if (arg_type && arg_type->isReference()) {
      // taking the address of this argument.
      arg_expr_env.result_lval = &arg_value;
    }
    else {
      arg_expr_env.result_rval = &arg_value;
      arg_expr_env.SetResultType(arg_type);
    }

    ProcessExpression(arg_expr_env, arg->expr);
    arguments->PushBack(arg_value);
    arg_ind++;
  }

  // fill in any default arguments not supplied at the call site.
  if (type) {
    while (arg_ind < type->params.count()) {
      Variable *var = type->params.nth(arg_ind);

      if (!var->value) {
        // out of default arguments, whatever. just bail out.
        return;
      }

      Xgill::Exp *arg_value;
      ExprEnv arg_expr_env(pre_point);

      if (var->type->isReference()) {
        // again, take the address for this argument.
        arg_expr_env.result_lval = &arg_value;
      }
      else {
        arg_expr_env.result_rval = &arg_value;
        arg_expr_env.SetResultType(var->type);
      }

      ProcessExpression(arg_expr_env, var->value);
      arguments->PushBack(arg_value);
      arg_ind++;
    }
  }
}

// get the return lvalue to assign a call result to, based on the expression
// environment in which that call result will be used. if return_early is set
// then the caller can return without further processing of expr_env after
// doing the call.
Xgill::Exp* GetCallReturnLval(const ExprEnv &expr_env,
                              Xgill::Type *return_type,
                              bool result_required, bool result_reference,
                              bool *return_early)
{
  *return_early = false;

  // compute the result lvalue to use. this can be one of three options:
  // - NULL, if the expression value will not be used.
  // - the assign result, if we need to store the expression value
  //   in another lvalue and can do it directly.
  // - a new temporary variable, otherwise.

  if (expr_env.IsResultUsed() || result_required) {
    if (expr_env.result_assign != NULL && expr_env.result_assign_op == BIN_ASSIGN) {
      // the assignment is direct if either:
      // - the retval is not a reference and we are not taking the address.
      // - the retval is a reference and we are taking the address.
      // making the assignment direct consumes the assign result reference.
      if (expr_env.result_assign_address == result_reference) {
        *return_early = true;
        expr_env.result_assign->MoveRef(&expr_env, NULL);
        return expr_env.result_assign;
      }
    }

    // we need to make a temporary variable to hold the result.
    return_type->IncRef();
    return GetNewTemporary(return_type);
  }
  else {
    *return_early = true;
    return NULL;
  }
}

void DoAllocateCall(Xgill::Location *loc, PPoint *pre_point,
                    const char *function_name,
                    Xgill::Exp *return_lval, Xgill::Exp *size_arg)
{
  // construct a function type for the call signature: void* fn(size_t).
  // TODO: make sure we are accounting for overflows correctly.

  Xgill::Type *void_type = Xgill::Type::MakeVoid();
  Xgill::Type *ptr_void_type =
    Xgill::Type::MakePointer(void_type, POINTER_WIDTH);

  Xgill::Type *size_type = Xgill::Type::MakeInt(POINTER_WIDTH, false);
  Xgill::Vector<Xgill::Type*> argument_types;
  argument_types.PushBack(size_type);

  Xgill::TypeFunction *func_type =
    Xgill::Type::MakeFunction(ptr_void_type, NULL, false, argument_types);
  Xgill::Exp *function = GetFunctionLval(function_name);

  Xgill::Vector<Xgill::Exp*> arguments;
  arguments.PushBack(size_arg);

  // get a point for after the allocation.
  loc->IncRef();
  PPoint after_point = benv->cfg->AddPoint(loc);

  Xgill::PEdge *edge =
    Xgill::PEdge::MakeCall(*pre_point, after_point,
                           func_type, return_lval, function, arguments);
  benv->cfg->AddEdge(edge);

  *pre_point = after_point;
}

void DoFreeCall(Xgill::Location *loc,
                PPoint *pre_point, const char *function_name,
                Xgill::Exp *base_arg)
{
  // construct a function type for the call signature: void fn(void*)

  Xgill::Type *void_type = Xgill::Type::MakeVoid();
  Xgill::Type *ptr_void_type =
    Xgill::Type::MakePointer(void_type, POINTER_WIDTH);
  void_type->IncRef();

  Xgill::Vector<Xgill::Type*> argument_types;
  argument_types.PushBack(ptr_void_type);

  Xgill::TypeFunction *func_type = (Xgill::TypeFunction*)
    Xgill::Type::MakeFunction(void_type, NULL, false, argument_types);
  Xgill::Exp *function = GetFunctionLval(function_name);

  Xgill::Vector<Xgill::Exp*> arguments;
  arguments.PushBack(base_arg);

  // get a point for after the deallocation.
  loc->IncRef();
  PPoint after_point = benv->cfg->AddPoint(loc);

  Xgill::PEdge *edge =
    Xgill::PEdge::MakeCall(*pre_point, after_point,
                           func_type, NULL, function, arguments);
  benv->cfg->AddEdge(edge);

  *pre_point = after_point;
}

// handle annotation functions like __ubound.
Xgill::Exp* DoAnnotateCall(const ExprEnv &expr_env,
                           const char *name, E_funCall *expr)
{
  if (!annotate.IsSpecified())
    return NULL;

  Xgill::Vector<Xgill::Exp*> arguments;
  DoCallArguments(expr_env.pre_point, NULL, expr->args, &arguments);

  Xgill::AnnotateKind annotate_kind = Xgill::AK_Invalid;

  if (strcmp(name, "lbound") == 0)
    annotate_kind = Xgill::AK_Lower;

  if (strcmp(name, "ubound") == 0)
    annotate_kind = Xgill::AK_Upper;

  if (strcmp(name, "zterm") == 0)
    annotate_kind = Xgill::AK_Zterm;

  if (strcmp(name, "loop_entry") == 0)
    annotate_kind = Xgill::AK_LoopEntry;

  if (annotate_kind) {
    if (arguments.Size() != 1) {
      cout << "ERROR: " << name << " must be used with a single argument" << endl;

      // use a fake variable so we bail out later.
      Xgill::String *fake_name = Xgill::String::Make("__unknown__");
      Xgill::Variable *fake_var =
        Xgill::Variable::Make(NULL, Xgill::VK_Local, fake_name, 0, NULL);

      return Xgill::Exp::MakeVar(fake_var);
    }
    else {
      Xgill::Exp *target = arguments[0];
      return Xgill::Exp::MakeAnnotate(annotate_kind, target);
    }
  }

  for (size_t ind = 0; ind < arguments.Size(); ind++)
    arguments[ind]->DecRef();

  return NULL;
}

void ProcessExpressionResult(const ExprEnv &expr_env,
                             Xgill::Exp *res, Type *res_type)
{
  Assert(res);
  Assert(res_type && !res_type->isReference());

  Xgill::Location *loc = benv->cfg->GetPointLocation(*expr_env.pre_point);

  if (expr_env.result_branch) {
    // we need two references on this value for the two edges.
    res->IncRef();

    Xgill::PEdge *true_edge =
      Xgill::PEdge::MakeAssume(*expr_env.pre_point, expr_env.true_point,
                               res, true);
    Xgill::PEdge *false_edge =
      Xgill::PEdge::MakeAssume(*expr_env.pre_point, expr_env.false_point,
                               res, false);

    benv->cfg->AddEdge(true_edge);
    benv->cfg->AddEdge(false_edge);
  }
  else if (expr_env.result_assign) {
    loc->IncRef();
    PPoint after_point = benv->cfg->AddPoint(loc);

    Type *lhs_type = expr_env.result_assign_type;
    Assert(!lhs_type->isReference());

    size_t res_bits;
    bool res_sign;
    GetTypeBits(res_type, &res_bits, &res_sign);

    size_t lval_bits;
    bool lval_sign;
    GetTypeBits(lhs_type, &lval_bits, &lval_sign);

    // add an implicit coercion to the result if needed.
    if (lval_bits != res_bits || lval_sign != res_sign)
      res = Xgill::Exp::MakeUnop(Xgill::U_Coerce, res, lval_bits, lval_sign);

    Xgill::Type *assign_type = GetType(lhs_type);

    Xgill::Exp *assign_rhs = NULL;
    if (expr_env.result_assign_op == BIN_ASSIGN) {
      if (expr_env.result_assign_address) {
        // this is a pointer assignment.
        assign_type = Xgill::Type::MakePointer(assign_type, POINTER_WIDTH);

        // assignment of the address of the rhs.
        // note that if the rhs is a reference type as well, this undoes the
        // ReferenceAddDrf() we added in ProcessExpression to res.
        assign_rhs = GetValueReference(expr_env.pre_point, res_type, res);
      }
      else {
        // plain direct assignment.
        assign_rhs = res;
      }
    }
    else {
      Assert(!expr_env.result_assign_address);

      expr_env.result_assign->IncRef();
      Xgill::Exp *drf_result = Xgill::Exp::MakeDrf(expr_env.result_assign);

      assign_rhs = ProcessBinop(lhs_type, res_type, lhs_type,
                                expr_env.result_assign_op, drf_result, res);
    }

    // special case that can arise when assigning string constants
    // to character arrays. we want to assign *string rather than string
    // to the array. TODO: should call memcpy instead.
    if (expr_env.result_assign_type->isArrayType()) {
      assign_rhs = Xgill::Exp::MakeDrf(assign_rhs);

      // cout << "WARNING: adding direct assignment between arrays: "
      //      << expr_env.result_assign << " := " << assign_rhs << endl;
    }

    expr_env.result_assign->MoveRef(&expr_env, NULL);
    Xgill::PEdge *edge =
      Xgill::PEdge::MakeAssign(*expr_env.pre_point, after_point, assign_type,
                               expr_env.result_assign, assign_rhs);
    benv->cfg->AddEdge(edge);

    *expr_env.pre_point = after_point;
  }
  else if (expr_env.result_lval) {
    // get the address of the result value.
    *expr_env.result_lval =
      GetValueReference(expr_env.pre_point, res_type, res);
  }
  else if (expr_env.result_rval) {
    if (expr_env.result_rval_bits) {
      // check if we need to add an implicit coercion.

      size_t res_bits;
      bool res_sign;
      GetTypeBits(res_type, &res_bits, &res_sign);

      if (res_bits != expr_env.result_rval_bits ||
          res_sign != expr_env.result_rval_sign)
        res = Xgill::Exp::MakeUnop(Xgill::U_Coerce, res,
                                   expr_env.result_rval_bits,
                                   expr_env.result_rval_sign);
    }

    *expr_env.result_rval = res;
  }
  else {
    res->DecRef();
  }
}

void ProcessExpression(const ExprEnv &expr_env, Expression *expr)
{
  Assert(expr);
  Assert(expr->type);

  // make sure we initialize any locations the caller receives data through.
  if (expr_env.result_lval)
    *expr_env.result_lval = NULL;
  if (expr_env.result_rval)
    *expr_env.result_rval = NULL;

  if (expr_env.ctor_instance_lval)
    Assert(expr->isE_constructor() || expr->isE_assign());

  Xgill::Location *loc = benv->cfg->GetPointLocation(*expr_env.pre_point);

  size_t bits;
  bool sign;
  GetTypeBits(expr->type->asRval(), &bits, &sign);

  Xgill::Exp *res = NULL;

  switch (expr->kind()) {

  case Expression::E_BOOLLIT: {
    E_boolLit *nexpr = expr->asE_boolLit();

    // constant fold branches on constant values.
    if (expr_env.result_branch) {
      PPoint target = nexpr->b ? expr_env.true_point : expr_env.false_point;
      AddSkipEdge(*expr_env.pre_point, target);
      return;
    }

    long value = nexpr->b ? 1 : 0;
    res = Xgill::Exp::MakeInt(value);
    break;
  }

  case Expression::E_INTLIT: {
    E_intLit *nexpr = expr->asE_intLit();

    // get the mpz bigint representation of the string and do error checking
    // on the string format.
    mpz_t value;
    mpz_init(value);

    if (!Xgill::StringToInt(nexpr->text, value))
      Assert(false);

    // constant fold branches on constant values.
    if (expr_env.result_branch) {
      PPoint target;
      if (mpz_cmp_si(value, 0))
        target = expr_env.true_point;
      else
        target = expr_env.false_point;
      AddSkipEdge(*expr_env.pre_point, target);

      mpz_clear(value);
      return;
    }

    res = Xgill::Exp::MakeIntMpz(value, bits, sign);
    mpz_clear(value);
    break;
  }

  case Expression::E_FLOATLIT: {
    E_floatLit *nexpr = expr->asE_floatLit();
    res = Xgill::Exp::MakeFloat(nexpr->text);
    break;
  }

  case Expression::E_STRINGLIT: {
    E_stringLit *nexpr = expr->asE_stringLit();

    // get the text of the string literal, including escape sequences
    // and quotes on either side.
    const char *final_text = nexpr->text;

    if (nexpr->continuation != NULL) {
      // more than one string constant. catenate them all into a single buffer.
      E_stringLit *cur = nexpr;
      while (cur != NULL) {
        int len = strlen(cur->text);
        scratch_buf_one.Append(cur->text, len);
        cur = cur->continuation;
      }
      scratch_buf_one.Ensure(1);
      *scratch_buf_one.pos++ = 0;

      final_text = (const char*) scratch_buf_one.base;
    }

    // remove quote marks and handle escape sequences.
    if (!Xgill::UnescapeStringLiteral(final_text, &scratch_buf_two))
      Assert(false);
    size_t lit_size = scratch_buf_two.pos - scratch_buf_two.base;

    if (nexpr->continuation != NULL)
      scratch_buf_one.Reset();

    // the result of this expression is a char[] reference. make an lvalue for
    // the string array and take its address.
    Xgill::TypeArray *carr_type = GetType(expr->type->asRval())->AsArray();

    Xgill::DataString *data_text =
      Xgill::DataString::Make(scratch_buf_two.base, lit_size);
    scratch_buf_two.Reset();

    res = Xgill::Exp::MakeString(carr_type, data_text);
    break;
  }

  case Expression::E_CHARLIT: {
    E_charLit *nexpr = expr->asE_charLit();

    char val;
    if (!Xgill::UnescapeCharLiteral(nexpr->text, &val))
      Assert(false);

    res = Xgill::Exp::MakeInt(val);
    break;
  }

  case Expression::E_THIS: {
    // type of this expression is str* for the underlying type.
    Xgill::Variable *var =
      Xgill::Variable::Make(benv->GetVariableId(),
                            Xgill::VK_This, NULL, 0, NULL);

    var->IncRef();
    benv->cfg->AddVariable(var, GetType(expr->type));

    Xgill::Exp *this_exp = Xgill::Exp::MakeVar(var);
    res = Xgill::Exp::MakeDrf(this_exp);
    break;
  }

  case Expression::E_VARIABLE: {
    E_variable *nexpr = expr->asE_variable();

    Type *var_type = NULL;
    if (nexpr->var)
      var_type = nexpr->var->type;

    // check for enumerator constants.
    if (nexpr->var && nexpr->var->isEnumerator()) {
      int value = nexpr->var->getEnumeratorValue();
      res = Xgill::Exp::MakeInt(value);
    }
    else {
      Xgill::Variable *var = GetVariable(nexpr->var, nexpr->name);
      Xgill::Exp *var_exp = Xgill::Exp::MakeVar(var);
      res = Xgill::Exp::MakeDrf(var_exp);

      res = ArrayRemoveDrf(expr_env, var_type, res);
      res = ReferenceAddDrf(var_type, res);
    }
    break;
  }

  case Expression::E_FIELDACC: {
    E_fieldAcc *nexpr = expr->asE_fieldAcc();
    Xgill::Exp *fld_exp = NULL;

    if (nexpr->field && nexpr->field->isStatic()) {
      // static field access on an unnecessary object.

      // process the expression in case there are side effects.
      ExprEnv obj_expr_env(expr_env.pre_point);
      ProcessExpression(obj_expr_env, nexpr->obj);

      Xgill::Variable *var =
        GetVariable(nexpr->field, nexpr->fieldName);
      fld_exp = Xgill::Exp::MakeVar(var);
    }
    else {
      // regular field access.

      Xgill::Exp *obj_lval;
      ExprEnv obj_expr_env(expr_env.pre_point);
      obj_expr_env.result_lval = &obj_lval;
      ProcessExpression(obj_expr_env, nexpr->obj);

      Xgill::Field *field = GetVariableField(nexpr->field, nexpr->fieldName);
      fld_exp = Xgill::Exp::MakeFld(obj_lval, field);
    }

    res = Xgill::Exp::MakeDrf(fld_exp);

    Type *field_type = NULL;
    if (nexpr->field)
      field_type = nexpr->field->type;

    res = ArrayRemoveDrf(expr_env, field_type, res);
    res = ReferenceAddDrf(field_type, res);
    break;
  }

  case Expression::E_ASSIGN: {
    E_assign *nexpr = expr->asE_assign();

    ExprEnv lhs_expr_env(expr_env.pre_point);

    Xgill::Exp *lhs_lval;
    if (expr_env.ctor_instance_lval) {
      // if the ctor is the builtin default copy constructor, the expression
      // we see here is just an assignment, in which case the instance object
      // becomes the assignment LHS.
      lhs_lval = expr_env.ctor_instance_lval;
    }
    else {
      lhs_expr_env.result_lval = &lhs_lval;
      ProcessExpression(lhs_expr_env, nexpr->target);
    }

    ExprEnv rhs_expr_env(expr_env.pre_point);
    rhs_expr_env.SetResultAssign(lhs_lval, nexpr->target->type->asRval(),
                                 false, nexpr->op);
    ProcessExpression(rhs_expr_env, nexpr->src);

    // expression result is the value of lhs_lval. this has reference type
    // so a parent expression can remove the Drf() and get lhs_lval itself.
    lhs_lval->IncRef();
    res = Xgill::Exp::MakeDrf(lhs_lval);
    break;
  }

  case Expression::E_UNARY: {
    E_unary *nexpr = expr->asE_unary();

    switch (nexpr->op) {
    case UNY_PLUS: {
      // this is a nop expression. recurse with the same ExprEnv on the operand.
      ProcessExpression(expr_env, nexpr->expr);
      return;
    }

    case UNY_NOT: {
      // if this is used to determine a branch just invert the true/false
      // branches and recurse.
      if (expr_env.result_branch) {
        ExprEnv oper_expr_env(expr_env.pre_point);
        oper_expr_env.SetResultBranch(expr_env.false_point,
                                      expr_env.true_point);
        ProcessExpression(oper_expr_env, nexpr->expr);
        return;
      }

      // otherwise fall through and treat this as a regular unary operation.
    }
    case UNY_MINUS:
    case UNY_BITNOT: {
      ExprEnv oper_expr_env(expr_env.pre_point);

      Xgill::Exp *oper_value;
      oper_expr_env.result_rval = &oper_value;
      ProcessExpression(oper_expr_env, nexpr->expr);

      Xgill::UnopKind new_unop = Xgill::U_Invalid;
      if (nexpr->op == UNY_NOT)
        new_unop = Xgill::U_LogicalNot;
      if (nexpr->op == UNY_MINUS)
        new_unop = Xgill::U_Neg;
      if (nexpr->op == UNY_BITNOT)
        new_unop = Xgill::U_BitwiseNot;
      Assert(new_unop != Xgill::U_Invalid);

      res = Xgill::Exp::MakeUnop(new_unop, oper_value, bits, sign);
      break;
    }

    default:
      Assert(false);
    }

    break;
  }

  case Expression::E_EFFECT: {
    E_effect *nexpr = expr->asE_effect();

    // if the result is totally ignored we can convert post-incr/decr into
    // pre-incr/decr, which do not require us to create temporaries.
    bool res_used = expr_env.IsResultUsed();

    bool incr;
    EffectOp op = nexpr->op;
    switch (op) {
    case EFF_PREINC: incr = true; break;
    case EFF_PREDEC: incr = false; break;
    case EFF_POSTINC: incr = true; if (!res_used) op = EFF_PREINC; break;
    case EFF_POSTDEC: incr = false; if (!res_used) op = EFF_PREDEC; break;
    default: Assert(false);
    }

    ExprEnv child_expr_env(expr_env.pre_point);

    Xgill::Exp *child_lval;
    child_expr_env.result_lval = &child_lval;
    ProcessExpression(child_expr_env, nexpr->expr);

    // get a second reference for when this is used as an assignment lhs.
    child_lval->IncRef();

    Type *lhs_type = nexpr->expr->type->asRval();

    // type for the final increment/decrement.
    Xgill::Type *new_lhs_type = GetType(lhs_type);

    Xgill::Exp *child_value = Xgill::Exp::MakeDrf(child_lval);
    Xgill::Exp *one_value = Xgill::Exp::MakeInt(1);

    // get a second reference on the value and compute the overall
    // result of the expression. this is either the plain expression value
    // (pre-incr/decr), or the value of a temporary which holds the
    // initial value (post-incr/decr).
    child_value->IncRef();
    if (op == EFF_PREINC || op == EFF_PREDEC)
    {
      res = child_value;
    }
    else if (op == EFF_POSTINC || op == EFF_POSTDEC)
    {
      // introduce a temporary to hold the expression result.
      new_lhs_type->IncRef();
      Xgill::Exp *temp_lval = GetNewTemporary(new_lhs_type);

      // expression result is the temporary's value.
      temp_lval->IncRef();
      res = Xgill::Exp::MakeDrf(temp_lval);

      // point for after the temporary assignment.
      loc->IncRef();
      PPoint temp_point = benv->cfg->AddPoint(loc);

      new_lhs_type->IncRef();
      Xgill::PEdge *temp_edge =
        Xgill::PEdge::MakeAssign(*expr_env.pre_point, temp_point,
                                 new_lhs_type, temp_lval, child_value);
      benv->cfg->AddEdge(temp_edge);

      *expr_env.pre_point = temp_point;
    }
    else {
      Assert(false);
    }

    Xgill::Exp *new_value =
      ProcessBinop(lhs_type, NULL, lhs_type,
                   (incr ? BIN_PLUS : BIN_MINUS),
                   child_value, one_value);

    // point for after the increment/decrement operation.
    loc->IncRef();
    PPoint after_point = benv->cfg->AddPoint(loc);

    Xgill::PEdge *update_edge =
      Xgill::PEdge::MakeAssign(*expr_env.pre_point, after_point,
                               new_lhs_type, child_lval, new_value);
    benv->cfg->AddEdge(update_edge);

    *expr_env.pre_point = after_point;
    break;
  }

  case Expression::E_BINARY: {
    E_binary *nexpr = expr->asE_binary();

    if (nexpr->op == BIN_COMMA) {
      // comma operation generates side effects for its left value then drops the result.
      ExprEnv empty_expr_env(expr_env.pre_point);
      ProcessExpression(empty_expr_env, nexpr->e1);
      ProcessExpression(expr_env, nexpr->e2);
      return;
    }
    else if (nexpr->op == BIN_AND || nexpr->op == BIN_OR) {
      // handle short circuiting for logical and/or operations.

      if (expr_env.result_branch) {
        // get a point for where the left expression jumps if it fails
        // to short circuit the operation.
        loc->IncRef();
        Xgill::PPoint fail_point = benv->cfg->AddPoint(loc);

        ExprEnv left_expr_env(expr_env.pre_point);
        if (nexpr->op == BIN_AND)
          left_expr_env.SetResultBranch(fail_point, expr_env.false_point);
        else
          left_expr_env.SetResultBranch(expr_env.true_point, fail_point);
        ProcessExpression(left_expr_env, nexpr->e1);

        ExprEnv right_expr_env(&fail_point);
        right_expr_env.SetResultBranch(expr_env.true_point,
                                       expr_env.false_point);
        ProcessExpression(right_expr_env, nexpr->e2);

        return;
      }
      else {
        // construct a true_point/false_point which assigns 1 or 0 to a temporary,
        // and recurse on this same expression.

        loc->IncRef();
        Xgill::PPoint true_point = benv->cfg->AddPoint(loc);

        loc->IncRef();
        Xgill::PPoint false_point = benv->cfg->AddPoint(loc);

        ExprEnv retry_expr_env(expr_env.pre_point);
        retry_expr_env.SetResultBranch(true_point, false_point);
        ProcessExpression(retry_expr_env, expr);

        loc->IncRef();
        Xgill::PPoint join_point = benv->cfg->AddPoint(loc);

        Xgill::Type *temp_type = GetType(expr->type);
        Xgill::Exp *temp_lval = GetNewTemporary(temp_type);
        temp_lval->IncRef();  // reference for second assignment.
        temp_lval->IncRef();  // reference for result

        Xgill::Exp *zero_value = Xgill::Exp::MakeInt(0);
        Xgill::Exp *one_value = Xgill::Exp::MakeInt(1);

        temp_type->IncRef();
        Xgill::PEdge *zero_edge =
          Xgill::PEdge::MakeAssign(false_point, join_point, temp_type,
                                   temp_lval, zero_value);
        benv->cfg->AddEdge(zero_edge);

        temp_type->IncRef();
        Xgill::PEdge *one_edge =
          Xgill::PEdge::MakeAssign(true_point, join_point, temp_type,
                                   temp_lval, one_value);
        benv->cfg->AddEdge(one_edge);

        *expr_env.pre_point = join_point;
        res = Xgill::Exp::MakeDrf(temp_lval);
      }
    }
    else if (nexpr->op == BIN_DOT_STAR || nexpr->op == BIN_ARROW_STAR) {
      // indirect field access operations. we are incomplete here:
      // evaluate the right side for side effects and just access
      // an error field of the left side.

      Xgill::Exp *left_value;
      ExprEnv left_expr_env(expr_env.pre_point);
      left_expr_env.result_rval = &left_value;
      ProcessExpression(left_expr_env, nexpr->e1);

      ExprEnv right_expr_env(expr_env.pre_point);
      ProcessExpression(right_expr_env, nexpr->e2);

      Xgill::Exp *left_lval;
      if (nexpr->op == BIN_DOT_STAR) {
        // need to take the address of the LHS.
        left_lval = ExpDereference(left_value);
        left_lval->IncRef();
        left_value->DecRef();
      }
      else {
        left_lval = left_value;
      }

      Xgill::Field *field = MakeErrorField(NULL);
      Xgill::Exp *fld_exp = Xgill::Exp::MakeFld(left_lval, field);
      res = Xgill::Exp::MakeDrf(fld_exp);

      Type *field_type = nexpr->e2->type;

      res = ArrayRemoveDrf(expr_env, field_type, res);
      res = ReferenceAddDrf(field_type, res);
    }
    else {
      // generic binary operation.

      ExprEnv left_expr_env(expr_env.pre_point);
      ExprEnv right_expr_env(expr_env.pre_point);

      Type *left_type = nexpr->e1->type->asRval();
      Type *right_type = nexpr->e2->type->asRval();

      // get a consistent type for the left and right operands.
      Type *op_type = usualArithmeticConversions(benv->base_env.tfac,
                                                 left_type, right_type);

      Xgill::Exp *left_value;
      left_expr_env.result_rval = &left_value;
      left_expr_env.SetResultType(op_type);

      Xgill::Exp *right_value;
      right_expr_env.result_rval = &right_value;
      right_expr_env.SetResultType(op_type);

      // force the result type to unsigned for bitwise operations.
      if (nexpr->op == BIN_BITAND ||
          nexpr->op == BIN_BITXOR ||
          nexpr->op == BIN_BITOR) {
        left_expr_env.result_rval_sign = false;
        right_expr_env.result_rval_sign = false;
      }

      ProcessExpression(left_expr_env, nexpr->e1);
      ProcessExpression(right_expr_env, nexpr->e2);

      res = ProcessBinop(nexpr->e1->type, nexpr->e2->type, nexpr->type,
                         nexpr->op, left_value, right_value);
    }

    break;
  }

  case Expression::E_ADDROF: {
    E_addrOf *nexpr = expr->asE_addrOf();

    ExprEnv child_expr_env(expr_env.pre_point);
    child_expr_env.result_lval = &res;
    ProcessExpression(child_expr_env, nexpr->expr);
    break;
  }

  case Expression::E_DEREF: {
    E_deref *nexpr = expr->asE_deref();

    ExprEnv child_expr_env(expr_env.pre_point);

    Xgill::Exp *ptr_value;
    child_expr_env.result_rval = &ptr_value;
    ProcessExpression(child_expr_env, nexpr->ptr);

    res = Xgill::Exp::MakeDrf(ptr_value);

    // the deref'ed expression must have either pointer or error type.
    Type *base_type = nexpr->ptr->type->asRval();
    Type *drf_type = NULL;
    if (base_type->isPointerType())
      drf_type = base_type->asPointerType()->atType;

    res = ArrayRemoveDrf(expr_env, drf_type, res);
    break;
  }

  case Expression::E_COND: {
    E_cond *nexpr = expr->asE_cond();

    // get a point for the result of the cond being true.
    loc->IncRef();
    PPoint true_point = benv->cfg->AddPoint(loc);

    // get a point for the result of the cond being false.
    loc->IncRef();
    PPoint false_point = benv->cfg->AddPoint(loc);

    ExprEnv cond_expr_env(expr_env.pre_point);
    cond_expr_env.SetResultBranch(true_point, false_point);
    ProcessExpression(cond_expr_env, nexpr->cond);

    // get a point for the join along the two branches.
    loc->IncRef();
    PPoint join_point = benv->cfg->AddPoint(loc);

    if (!expr_env.result_lval && !expr_env.result_rval) {
      // we are not directly observing the result of the condition,
      // so we do not need a temporary. just make new environments
      // and recurse, then connect them at the join points.

      ExprEnv true_expr_env(&true_point);
      ExprEnv false_expr_env(&false_point);
      if (expr_env.result_branch) {
        true_expr_env.SetResultBranch(expr_env.true_point,
                                      expr_env.false_point);
        false_expr_env.SetResultBranch(expr_env.true_point,
                                       expr_env.false_point);
      }
      else if (expr_env.result_assign) {
        expr_env.result_assign->IncRef();
        expr_env.result_assign->IncRef();
        true_expr_env.SetResultAssign(expr_env.result_assign,
                                      expr_env.result_assign_type,
                                      expr_env.result_assign_address,
                                      expr_env.result_assign_op);
        false_expr_env.SetResultAssign(expr_env.result_assign,
                                       expr_env.result_assign_type,
                                       expr_env.result_assign_address,
                                       expr_env.result_assign_op);

        // dispose of the reference held for expr_env. this won't be needed.
        expr_env.result_assign->DecRef(&expr_env);
      }

      ProcessExpression(true_expr_env, nexpr->th);
      ProcessExpression(false_expr_env, nexpr->el);

      if (!expr_env.result_branch) {
        AddSkipEdge(true_point, join_point);
        AddSkipEdge(false_point, join_point);
      }

      // this recursion takes care of the possible cases.
      if (!expr_env.result_branch)
        *expr_env.pre_point = join_point;
      return;
    }
    else {
      // generate a temporary and assign it either the address of the
      // true or false branch, or the value of the true or false branch,
      // depending on whether we want the lvalue or rvalue of the branches.

      Type *type = expr->type->asRval();
      Xgill::Exp *temp_lval = MakeResultTemporary(expr_env, type);
      temp_lval->IncRef();  // get reference for both assignments.

      ExprEnv true_expr_env(&true_point);
      true_expr_env.SetResultAssign(temp_lval, type,
                                    expr_env.ResultAddressNeeded());
      ProcessExpression(true_expr_env, nexpr->th);

      ExprEnv false_expr_env(&false_point);
      false_expr_env.SetResultAssign(temp_lval, type,
                                     expr_env.ResultAddressNeeded());
      ProcessExpression(false_expr_env, nexpr->el);

      AddSkipEdge(true_point, join_point);
      AddSkipEdge(false_point, join_point);

      temp_lval->IncRef();
      res = GetResultTemporaryValue(expr_env, temp_lval);
      *expr_env.pre_point = join_point;
    }

    break;
  }

  case Expression::E_GNUCOND: {
    E_gnuCond *nexpr = expr->asE_gnuCond();

    // get a point for the result of the cond being false.
    loc->IncRef();
    PPoint false_point = benv->cfg->AddPoint(loc);

    // get a point for the join along the two branches.
    loc->IncRef();
    PPoint join_point = benv->cfg->AddPoint(loc);

    // ditto for E_COND, generate a temporary to hold the value of the result.

    Type *type = nexpr->cond->type->asRval();
    Xgill::Exp *temp_lval = MakeResultTemporary(expr_env, type);
    temp_lval->IncRef(); // reference for second assignment.

    ExprEnv true_expr_env(expr_env.pre_point);
    true_expr_env.SetResultAssign(temp_lval, type,
                                  expr_env.ResultAddressNeeded());
    ProcessExpression(true_expr_env, nexpr->cond);

    ExprEnv false_expr_env(expr_env.pre_point);
    false_expr_env.SetResultAssign(temp_lval, type,
                                   expr_env.ResultAddressNeeded());
    ProcessExpression(false_expr_env, nexpr->el);

    AddSkipEdge(false_point, join_point);

    temp_lval->IncRef();
    res = GetResultTemporaryValue(expr_env, temp_lval);

    // connect the edges from the conditional test to the join point and
    // execution point of the else branch.
    res->IncRef();
    Xgill::PEdge *true_edge =
      Xgill::PEdge::MakeAssume(*expr_env.pre_point, join_point, res, true);
    res->IncRef();
    Xgill::PEdge *false_edge =
      Xgill::PEdge::MakeAssume(*expr_env.pre_point, false_point, res, false);

    benv->cfg->AddEdge(true_edge);
    benv->cfg->AddEdge(false_edge);

    *expr_env.pre_point = join_point;
    break;
  }

  case Expression::E_FUNCALL: {
    E_funCall *nexpr = expr->asE_funCall();

    // check to see if this is an operator overload we want to undo.
    // we only do this for assignments that use a builtin copy operator.
    if (E_fieldAcc *nfunc = nexpr->func->ifE_fieldAcc()) {
      if (nfunc->field && nfunc->field->isBuiltin && nexpr->replaceExpr) {
        ProcessExpression(expr_env, nexpr->replaceExpr);
        return;
      }
    }

    // remove superfluous dereferences on the function pointer expression.
    Expression *func_expr = nexpr->func;
    while (func_expr->isE_deref() && func_expr->type->isFunctionType())
      func_expr = func_expr->asE_deref()->ptr;

    // check to see if this is a baked-in function with special behavior.
    if (E_variable *nfunc_expr = func_expr->ifE_variable()) {
      const char *name = nfunc_expr->name->getName();
      res = DoAnnotateCall(expr_env, name, nexpr);

      if (res)
        break;
    }

    // whether this is a function pointer call. function pointer calls
    // (as distinguished from direct calls and instance function calls)
    // have a (func (*&)(...)) as the function expression type.
    bool is_function_pointer = false;

    // get the type of the function call. this will be NULL only if there was
    // a parse or type checking error and we couldn't figure out the type.
    FunctionType *base_func_type = NULL;

    Type *func_expr_type = func_expr->type->asRval();
    if (func_expr_type->isPointerType()) {
      // it would be nice to ensure that if we can't get the base function
      // type here that there was an explicit error type inserted.
      // however if parsing fails we might end up assigning bad types
      // rather than error types to global variables, so that the type
      // we are trying to invoke here could be anything at all.

      is_function_pointer = true;
      Type *tgt_func_type = func_expr_type->asPointerType()->atType;
      if (tgt_func_type->isFunctionType())
        base_func_type = tgt_func_type->asFunctionType();
    }
    else if (func_expr_type->isFunctionType()) {
      base_func_type = func_expr->type->asFunctionType();
    }

    // get a point for after the function call.
    loc->IncRef();
    PPoint after_point = benv->cfg->AddPoint(loc);

    // whether the result of the function is a reference.
    bool result_reference = false;

    Xgill::TypeFunction *func_type = NULL;
    if (base_func_type) {
      func_type = GetType(base_func_type)->AsFunction();
      result_reference = base_func_type->retType->isReferenceType();
    }
    else {
      func_type = GetErrorFunctionType();
    }

    Xgill::Vector<Xgill::Exp*> arguments;
    DoCallArguments(expr_env.pre_point, base_func_type,
                    nexpr->args, &arguments);

    bool return_early;
    Xgill::Exp *return_lval =
      GetCallReturnLval(expr_env, func_type->GetReturnType(),
                        false, result_reference, &return_early);

    if (func_expr->isE_fieldAcc() && !is_function_pointer) {
      E_fieldAcc *nfunc = func_expr->asE_fieldAcc();

      if (nfunc->field && nfunc->field->isStatic()) {
        // static function call on an (unnecessary) object.

        // process the expression in case there are side effects.
        ExprEnv obj_expr_env(expr_env.pre_point);
        ProcessExpression(obj_expr_env, nfunc->obj);

        Xgill::Variable *var =
          GetVariable(nfunc->field, nfunc->fieldName);
        Xgill::Exp *var_lval = Xgill::Exp::MakeVar(var);

        Xgill::PEdge *edge =
          Xgill::PEdge::MakeCall(*expr_env.pre_point, after_point,
                                 func_type, return_lval,
                                 var_lval, arguments);
        benv->cfg->AddEdge(edge);
      }
      else {
        // instance function call.

        Xgill::Exp *instance_object;
        ExprEnv obj_expr_env(expr_env.pre_point);
        obj_expr_env.result_lval = &instance_object;
        ProcessExpression(obj_expr_env, nfunc->obj);

        Xgill::Field *instance_field =
          GetVariableField(nfunc->field, nfunc->fieldName);

        Xgill::PEdge *edge =
          Xgill::PEdge::MakeCall(*expr_env.pre_point, after_point,
                                 func_type, return_lval,
                                 instance_object, instance_field, arguments);
        benv->cfg->AddEdge(edge);
      }
    }
    else {
      // direct or indirect call without an object.

      Xgill::Exp *function;
      ExprEnv func_expr_env(expr_env.pre_point);
      func_expr_env.result_lval = &function;
      ProcessExpression(func_expr_env, func_expr);

      if (is_function_pointer) {
        // for function pointer calls the dereference is not encoded
        // in the expression tree so add an extra one.
        function = Xgill::Exp::MakeDrf(function);
      }

      Xgill::PEdge *edge =
        Xgill::PEdge::MakeCall(*expr_env.pre_point, after_point,
                               func_type, return_lval,
                               function, arguments);
      benv->cfg->AddEdge(edge);
    }

    if (return_early) {
      // the call result assignment took care of everything
      // we needed to do.
      *expr_env.pre_point = after_point;
      return;
    }

    // the lvalue assigned to by the call is a temporary. take either *T
    // or **T as the result depending on whether the returned value
    // is a reference.

    Assert(return_lval);

    return_lval->IncRef();
    if (result_reference)
      return_lval = Xgill::Exp::MakeDrf(return_lval);
    res = Xgill::Exp::MakeDrf(return_lval);

    *expr_env.pre_point = after_point;
    break;
  }

  case Expression::E_CONSTRUCTOR: {
    E_constructor *nexpr = expr->asE_constructor();

    // get a point for after the constructor call.
    loc->IncRef();
    PPoint after_point = benv->cfg->AddPoint(loc);

    FunctionType *base_func_type = NULL;
    if (nexpr->ctorVar && nexpr->ctorVar->type &&
        nexpr->ctorVar->type->isFunctionType())
      base_func_type = nexpr->ctorVar->type->asFunctionType();

    Xgill::TypeFunction *func_type;
    if (base_func_type)
      func_type = GetType(base_func_type)->AsFunction();
    else
      func_type = GetErrorFunctionType();

    Xgill::Vector<Xgill::Exp*> arguments;
    DoCallArguments(expr_env.pre_point, base_func_type,
                    nexpr->args, &arguments);

    Xgill::Exp *instance_object;
    if (expr_env.ctor_instance_lval) {
      instance_object = expr_env.ctor_instance_lval;
    }
    else if (nexpr->retObj) {
      ExprEnv inst_expr_env(expr_env.pre_point);
      inst_expr_env.result_lval = &instance_object;
      ProcessExpression(inst_expr_env, nexpr->retObj);
    }
    else {
      // we need a new temporary. TODO: why are we getting here?
      instance_object = GetNewTemporary(GetType(expr->type));
    }

    Xgill::Field *instance_field = GetVariableField(nexpr->ctorVar);

    Xgill::PEdge *edge =
      Xgill::PEdge::MakeCall(*expr_env.pre_point, after_point, func_type, NULL,
                             instance_object, instance_field, arguments);
    benv->cfg->AddEdge(edge);

    instance_object->IncRef();
    res = Xgill::Exp::MakeDrf(instance_object);

    *expr_env.pre_point = after_point;
    break;
  }

  // INCOMPLETE
  case Expression::E_NEW: {
    E_new *nexpr = expr->asE_new();

    Xgill::Type *result_type = GetType(expr->type);

    bool return_early;
    Xgill::Exp *return_lval =
      GetCallReturnLval(expr_env, result_type,
                         true, false, &return_early);
    result_type->DecRef();

    int single_type_size;

    if (expr->type->isPointerType()) {
      Type *single_type = expr->type->asPointerType()->atType;
      benv->base_env.sizeofType(single_type, single_type_size, NULL);
    }
    else {
      // what are we constructing? it is a mystery. this should only come
      // up with parse/tcheck errors.
      single_type_size = 0;
    }

    Xgill::Exp *size_arg = Xgill::Exp::MakeInt(single_type_size);
    if (nexpr->arraySize) {
      Xgill::Exp *length_value;
      ExprEnv length_expr_env(expr_env.pre_point);
      length_expr_env.result_rval = &length_value;
      ProcessExpression(length_expr_env, nexpr->arraySize);

      size_arg = Xgill::Exp::MakeBinop(Xgill::B_Mult,
                                       size_arg, length_value, NULL,
                                       POINTER_BITS, false);
    }

    // generate the call to malloc.
    DoAllocateCall(loc, expr_env.pre_point, "malloc", return_lval, size_arg);

    // run the constructor on the result lvalue.
    // TODO: we are only running the constructor in the single element case.
    if (nexpr->ctorStatement && !nexpr->arraySize) {

      // instance object to use for the constructor expression.
      // the variable specified as the receiver for the E_constructor
      // is some temporary we aren't referring to.
      return_lval->IncRef();
      Xgill::Exp *ctor_instance_lval = Xgill::Exp::MakeDrf(return_lval);

      Expression *ctorExpr = nexpr->ctorStatement->asS_expr()->expr->expr;
      ExprEnv ctor_expr_env(expr_env.pre_point);
      ctor_expr_env.ctor_instance_lval = ctor_instance_lval;
      ProcessExpression(ctor_expr_env, ctorExpr);
    }

    if (return_early)
      return;

    return_lval->IncRef();
    res = Xgill::Exp::MakeDrf(return_lval);
    break;
  }

  // INCOMPLETE
  case Expression::E_DELETE: {
    E_delete *nexpr = expr->asE_delete();

    // run the destructor on the argument lvalue.
    // TODO: we are only running the destructor in the single element case.
    if (nexpr->dtorStatement && !nexpr->array)
      ProcessStatement(nexpr->dtorStatement, true, expr_env.pre_point);

    Xgill::Exp *arg_value;
    ExprEnv arg_expr_env(expr_env.pre_point);
    arg_expr_env.result_rval = &arg_value;
    ProcessExpression(arg_expr_env, nexpr->expr);

    // generate the call to free.
    DoFreeCall(loc, expr_env.pre_point, "free", arg_value);

    Assert(!expr_env.IsResultUsed());
    return;
  }

  case Expression::E_SIZEOF: {
    // the expression is not actually evaluated and generates no side effects.
    res = Xgill::Exp::MakeInt(expr->asE_sizeof()->size);
    break;
  }

  case Expression::E_SIZEOFTYPE: {
    res = Xgill::Exp::MakeInt(expr->asE_sizeofType()->size);
    break;
  }

  case Expression::E_ALIGNOFTYPE: {
    res = Xgill::Exp::MakeInt(expr->asE_alignofType()->alignment);
    break;
  }

  case Expression::E_ALIGNOFEXPR: {
    // the expression is not actually evaluated and generates no side effects.
    res = Xgill::Exp::MakeInt(expr->asE_alignofExpr()->alignment);
    break;
  }

  case Expression::E_CAST:
  case Expression::E_KEYWORDCAST: {
    Type *type;
    Expression *target;

    if (E_cast *nexpr = expr->ifE_cast()) {
      type = nexpr->ctype->getType();
      target = nexpr->expr;
    }
    else if (E_keywordCast *nexpr = expr->ifE_keywordCast()) {
      type = nexpr->ctype->getType();
      target = nexpr->expr;
    }
    else {
      Assert(false);
    }

    // generate U_coerce unops for casts to integer types.
    // otherwise ignore the cast.

    bool do_coerce = false;
    if (type->isSimpleType()) {
      const SimpleType *stype = type->asSimpleTypeC();
      if (isIntegerType(stype->type))
        do_coerce = true;
    }

    if (!do_coerce) {
      // nop the cast: recurse on the target expression and return.
      ProcessExpression(expr_env, target);
      return;
    }

    Xgill::Exp *target_value;
    ExprEnv target_expr_env(expr_env.pre_point);
    target_expr_env.result_rval = &target_value;
    ProcessExpression(target_expr_env, target);

    res = Xgill::Exp::MakeUnop(Xgill::U_Coerce, target_value, bits, sign);
    break;
  }

  case Expression::E_STATEMENT: {
    E_statement *nexpr = expr->asE_statement();

    benv->scopes.PushBack(ScopeEnv());
    ScopeEnv &scope_env = benv->scopes.Back();
    InitializeScope(scope_env, nexpr->s);

    int stmt_count = nexpr->s->stmts.count();

    // process all but the last statement as usual.
    for (int ind = 0; ind < stmt_count - 1; ind++) {
      Statement *child_stmt = nexpr->s->stmts.nth(ind);
      ProcessStatement(child_stmt, true, expr_env.pre_point);
    }

    // if the last statement is an expression with non-void type then
    // it is the result of this expression and we will get its value.
    // otherwise it has void value and process it as a normal statement.
    if (stmt_count != 0) {
      Statement *last_stmt = nexpr->s->stmts.nth(stmt_count - 1);
      S_expr *last_expr = last_stmt->ifS_expr();

      // the last statement might be a label.
      if (S_label *last_label = last_stmt->ifS_label())
        last_expr = last_label->s->ifS_expr();

      Type *last_type = NULL;
      if (last_expr)
        last_type = last_expr->expr->expr->type->asRval();

      if (last_type && !last_type->isVoid()) {
        // we can't just recurse with expr_env on the last statement
        // because we might have destructors that need to be called
        // at scope exit.

        Xgill::Exp *temp_lval = MakeResultTemporary(expr_env, last_type);

        ExprEnv child_expr_env(expr_env.pre_point);
        child_expr_env.SetResultAssign(temp_lval, last_type,
                                       expr_env.ResultAddressNeeded());
        ProcessExpression(child_expr_env, last_expr->expr->expr);

        temp_lval->IncRef();
        res = GetResultTemporaryValue(expr_env, temp_lval);
      }
      else {
        ProcessStatement(last_stmt, true, expr_env.pre_point);
      }
    }

    ScopeEnv back_scope_env = benv->scopes.Back();
    ProcessExitScope(back_scope_env, expr_env.pre_point);
    benv->scopes.PopBack();

    if (res == NULL) {
      Assert(!expr_env.IsResultUsed());
      return;
    }

    break;
  }

  case Expression::E_COMPOUNDLIT: {
    E_compoundLit *nexpr = expr->asE_compoundLit();

    Type *type = nexpr->stype->getType();

    bool return_early = false;
    Xgill::Exp *assign_lval = NULL;

    if (expr_env.result_assign && !expr_env.result_assign_address) {
      assign_lval = expr_env.result_assign;
      assign_lval->MoveRef(&expr_env, NULL);
      return_early = true;
    }
    else {
      // make a temporary to hold the result of the compound initializer.
      assign_lval = GetNewTemporary(GetType(type));
    }

    if (return_early) {
      ProcessInitializer(expr_env.pre_point, assign_lval, type, nexpr->init);
      return;
    }

    assign_lval->IncRef();
    res = Xgill::Exp::MakeDrf(assign_lval);

    ProcessInitializer(expr_env.pre_point, assign_lval, type, nexpr->init);
    break;
  }

  // INCOMPLETE
  case Expression::E___BUILTIN_CONSTANT_P:
  case Expression::E_TYPEUNARY:
  case Expression::E_TYPEBINARY: {
    // treat these as always returning false. we should be able to do better
    // with some of these, at least leave them uninterpreted.

    // constant fold branches.
    if (expr_env.result_branch) {
      AddSkipEdge(*expr_env.pre_point, expr_env.false_point);
      return;
    }

    res = Xgill::Exp::MakeInt(0);
    break;
  }

  // INCOMPLETE
  case Expression::E_THROW: {
    // we're not modelling exception handling yet so redirect any throws
    // to program termination (point 0 in the CFG).
    AddSkipEdge(*expr_env.pre_point, 0);

    // unreachable point for the fall through.
    loc->IncRef();
    *expr_env.pre_point = benv->cfg->AddPoint(loc);
    return;
  }

  // INCOMPLETE
  case Expression::E___BUILTIN_VA_ARG:
  case Expression::E___BUILTIN_VA_ARG_PACK: {
    // make a function call returning the appropriate type.

    Xgill::Type *ret_type = GetType(expr->type->asRval());
    Xgill::Vector<Xgill::Type*> argument_types;

    Xgill::TypeFunction *func_type =
      Xgill::Type::MakeFunction(ret_type, NULL, false, argument_types);
    Xgill::Exp *function = GetFunctionLval("__builtin_va_arg");

    bool return_early;
    Xgill::Exp *return_lval =
      GetCallReturnLval(expr_env, ret_type,
                        true, false, &return_early);
    Xgill::Vector<Xgill::Exp*> arguments;

    // get a point for after the call.
    loc->IncRef();
    PPoint after_point = benv->cfg->AddPoint(loc);

    Xgill::PEdge *edge =
      Xgill::PEdge::MakeCall(*expr_env.pre_point, after_point,
                             func_type, return_lval, function, arguments);
    benv->cfg->AddEdge(edge);

    *expr_env.pre_point = after_point;

    if (return_early)
      return;

    return_lval->IncRef();
    res = Xgill::Exp::MakeDrf(return_lval);
    break;
  }

  // INCOMPLETE
  case Expression::E_ADDROFLABEL: {

    // result is a local variable '$label' of type void.
    Xgill::String *name = Xgill::String::Make("$label");
    Xgill::Variable *var =
      Xgill::Variable::Make(benv->GetVariableId(),
                            Xgill::VK_Local, name, 0, NULL);
    Xgill::Type *type = Xgill::Type::MakeVoid();

    var->IncRef();
    benv->cfg->AddVariable(var, type);

    res = Xgill::Exp::MakeVar(var);
    break;
  }

  // not handled yet
  case Expression::E_TYPEIDEXPR:
  case Expression::E_TYPEIDTYPE:
    cout << "ERROR: Expression unimplemented: " << expr->kindName() << endl;
    Assert(false);
    break;

  // should never see.
  case Expression::E_ARROW:
  case Expression::E_GROUPING:
    cout << "ERROR: Unexpected expression: " << expr->kindName() << endl;
    Assert(false);

  default:
    Assert(false);
  }

  ProcessExpressionResult(expr_env, res, expr->type->asRval());
}

void ProcessCondition(const ExprEnv &expr_env,
                      Condition *cond)
{
  Assert(cond);

  switch (cond->kind()) {

  case Condition::CN_EXPR: {
    CN_expr *ncond = cond->asCN_expr();
    ProcessExpression(expr_env, ncond->expr->expr);
    break;
  }

  case Condition::CN_DECL: {
    CN_decl *ncond = cond->asCN_decl();
    Declarator *decl = ncond->typeId->decl;

    Xgill::Variable *var = GetVariable(decl->var);
    Xgill::Exp *var_lval = Xgill::Exp::MakeVar(var);

    ProcessInitializer(expr_env.pre_point, var_lval, 
                       decl->var->type, decl->init);

    size_t bits;
    bool sign;
    GetTypeBits(decl->var->type->asRval(), &bits, &sign);

    // compute the value of the lval. this is *T or **T (for reference vars).

    Xgill::Exp *var_value;
    var_lval->IncRef();
    if (decl->var->type->isReference()) {
      Xgill::Exp *var_drf = Xgill::Exp::MakeDrf(var_lval);
      var_value = Xgill::Exp::MakeDrf(var_drf);
    }
    else {
      var_value = Xgill::Exp::MakeDrf(var_lval);
    }

    ProcessExpressionResult(expr_env, var_value,
                            decl->var->type->asRval());
    break;
  }

  default:
    break;
  }
}

void ProcessConditionBranch(PPoint *pre_point,
                            PPoint true_point, PPoint false_point,
                            Condition *cond)
{
  ExprEnv expr_env(pre_point);
  expr_env.SetResultBranch(true_point, false_point);
  ProcessCondition(expr_env, cond);
}

// process an initializer appearing in a compound initializer for a struct
// or array. position is the expected field or subscript position in
// the parent struct/array, which might change if the child is a designated
// initializer. return value is the position which was initialized.
size_t ProcessChildInitializer(PPoint *pre_point,
                               Xgill::Exp *parent_lval, Type *parent_type,
                               size_t position, Initializer *child_init)
{
  if (!child_init->isIN_designated()) {
    // initialization with no designator. use the position to figure out
    // which field or array element to initialize.

    Xgill::Exp *update_lval;
    Type *update_type;

    if (parent_type->isArrayType()) {
      ArrayType *ntype = parent_type->asArrayType();

      Xgill::Exp *index_value = Xgill::Exp::MakeInt(position);
      Xgill::Type *elt_type = GetType(ntype->eltType);
      update_lval = Xgill::Exp::MakeIndex(parent_lval, elt_type, index_value);
      update_type = ntype->eltType;
    }
    else if (parent_type->isCompoundType()) {
      CompoundType *ntype = parent_type->asCompoundType();

      if ((int)position >= ntype->dataMembers.count()) {
        // we can see this if we had parse errors processing the type
        // and didn't get all the fields.
        ProcessFailure("ProcessChildInitializer()");
        parent_lval->DecRef();
        return position;
      }

      Variable *var_field = ntype->dataMembers.nth(position);
      Xgill::Field *field = GetVariableField(var_field);

      update_lval = Xgill::Exp::MakeFld(parent_lval, field);
      update_type = var_field->type;
    }
    else {
      // another place we can get if we encountered parse errors.
      ProcessFailure("ProcessChildInitializer()");
      parent_lval->DecRef();
      return position;
    }

    ProcessInitializer(pre_point, update_lval, update_type, child_init);
    return position;
  }

  IN_designated *ninit = child_init->asIN_designated();

  // the new position is the position of the first designator in the list.
  size_t new_position = 0;
  bool set_new_position = false;

  // current lvalues and the type shared by all of them at this point
  // in the designator crawl. there may be multiple lvalues if subscript
  // range initializers are used.
  Xgill::Vector<Xgill::Exp*> cur_lval_list;
  Type *cur_type = parent_type;

  // consume the reference on parent_lval passed to this.
  cur_lval_list.PushBack(parent_lval);

  FakeList<Designator> *designator_list = ninit->designator_list;
  while (designator_list != NULL) {
    Designator *dsig = designator_list->first();
    designator_list = designator_list->butFirst();

    Xgill::Vector<Xgill::Exp*> next_lval_list;

    switch (dsig->kind()) {
    case Designator::FIELDDESIGNATOR: {
      FieldDesignator *ndsig = dsig->asFieldDesignator();

      if (!cur_type->isCompoundType()) {
        Assert(cur_type->isError());
        goto error_return;
      }

      CompoundType *ntype = cur_type->asCompoundType();
      int field_pos = ntype->getDataMemberPosition(ndsig->id);

      if (field_pos == -1)
        goto error_return;

      if (!set_new_position) {
        new_position = field_pos;
        set_new_position = true;
      }

      Variable *var_field = ntype->dataMembers.nth(field_pos);
      Xgill::Field *field = GetVariableField(var_field);
      field->MoveRef(NULL, dsig);

      for (size_t tind = 0; tind < cur_lval_list.Size(); tind++) {
        field->IncRef();
        Xgill::Exp *cur_lval = cur_lval_list[tind];
        Xgill::Exp *fld_lval = Xgill::Exp::MakeFld(cur_lval, field);
        next_lval_list.PushBack(fld_lval);
      }

      field->DecRef(dsig);
      cur_type = var_field->type;
      break;
    }

    case Designator::SUBSCRIPTDESIGNATOR: {
      SubscriptDesignator *ndsig = dsig->asSubscriptDesignator();

      if (!cur_type->isArrayType()) {
        Assert(cur_type->isError());
        goto error_return;
      }

      ArrayType *ntype = cur_type->asArrayType();

      int rangeMin;
      int rangeMax;

      if (!ndsig->idx_expr->constEval(benv->base_env, rangeMin))
        goto error_return;
      if (ndsig->idx_expr2) {
        if (!ndsig->idx_expr2->constEval(benv->base_env, rangeMax))
          goto error_return;
      }
      else {
        rangeMax = rangeMin;
      }

      if (!set_new_position) {
        new_position = rangeMax;
        set_new_position = true;
      }

      Xgill::Type *elt_type = GetType(ntype->eltType);
      elt_type->MoveRef(NULL, dsig);

      for (size_t tind = 0; tind < cur_lval_list.Size(); tind++) {
        Xgill::Exp *cur_lval = cur_lval_list[tind];

        for (int pos = rangeMin; pos <= rangeMax; pos++) {
          elt_type->IncRef();
          cur_lval->IncRef();
          Xgill::Exp *index = Xgill::Exp::MakeInt(pos);
          Xgill::Exp *index_lval =
            Xgill::Exp::MakeIndex(cur_lval, elt_type, index);
          next_lval_list.PushBack(index_lval);
        }

        cur_lval->DecRef();
      }

      elt_type->DecRef(dsig);
      cur_type = ntype->eltType;
      break;
    }

    default:
      Assert(false);
    }

    // copy next lvalues into the current lvalues (whose references
    // have been consumed).
    cur_lval_list = next_lval_list;
  }

  for (size_t tind = 0; tind < cur_lval_list.Size(); tind++)
    ProcessInitializer(pre_point, cur_lval_list[tind],
                       cur_type, ninit->init);

  Assert(set_new_position);
  return new_position;

 error_return:

  ProcessFailure("ProcessChildInitializer()");

  // drop references on cur_lval_list and return original position.
  for (size_t tind = 0; tind < cur_lval_list.Size(); tind++)
    cur_lval_list[tind]->DecRef();

  return position;
}

void ProcessInitializer(PPoint *pre_point,
                        Xgill::Exp *assign_lval, Type *assign_type,
                        Initializer *init)
{
  Assert(init);

  switch (init->kind()) {

  case Initializer::IN_EXPR: {
    IN_expr *ninit = init->asIN_expr();

    ExprEnv expr_env(pre_point);
    expr_env.SetResultAssign(assign_lval,
                             assign_type->asRval(),
                             assign_type->isReference());
    return ProcessExpression(expr_env, ninit->e);
  }

  case Initializer::IN_COMPOUND: {
    IN_compound *ninit = init->asIN_compound();

    // TODO: zero out the structure here in case the initializers
    // omit array or structure elements.

    assign_lval->MoveRef(NULL, init);

    // check the count against the cutoff to limit the number of initializers
    // we process.
    int max_init = ninit->inits.count();

    if (max_init > INITIALIZER_CUTOFF) {
      cout << "WARNING: Large initializer encountered ("
           << ninit->inits.count()
           << " entries), skipping later entries..." << endl;
      max_init = INITIALIZER_CUTOFF;
    }

    size_t pos = 0;
    for (int ind = 0; ind < max_init; ind++) {
      Initializer *child_init = ninit->inits.nth(ind);

      assign_lval->IncRef();
      size_t upd_pos = ProcessChildInitializer(pre_point,
                                               assign_lval, assign_type,
                                               pos, child_init);

      // future initializers start after the just-initialized item.
      pos = upd_pos + 1;
    }

    assign_lval->DecRef(init);
    break;
  }

  // punt on constructors encountered here. this can come up if, for example,
  // an object with a constructor is declared in a branch condition.
  // we will end up treating these variables like they were uninitialized.
  case Initializer::IN_DESIGNATED:
  case Initializer::IN_CTOR:
    // cout << "ERROR: Unexpected initializer: " << assign_lval << endl;
    break;

  default:
    Assert(false);
    break;
  }
}
