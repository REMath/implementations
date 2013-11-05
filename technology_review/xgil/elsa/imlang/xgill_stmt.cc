// xgill_stmt.cc        see license.txt for copyright and terms of use
// translation of statements for xgill frontend.

#include "xgill.h"

// visitor to fill environment in with info on all labels
// and local variables in a function body.
class XgillBodyVisitor : public ASTVisitor
{
 public:
  Xgill::Vector<Statement*> stmt_list;

  virtual bool visitStatement(Statement *stmt)
  {
    if (S_label *nstmt = stmt->ifS_label()) {
      benv->labels.PushBack(LabelData());
      LabelData &data = benv->labels.Back();

      data.label = nstmt;

      Xgill::Location *loc = GetLocation(stmt->loc);
      data.point = benv->cfg->AddPoint(loc);

      // copy over the nested statements to this data.
      data.stmt_list = stmt_list;
    }

    stmt_list.PushBack(stmt);
    return true;
  }

  virtual void postvisitStatement(Statement *stmt)
  {
    Assert(stmt_list.Back() == stmt);
    stmt_list.PopBack();
  }

  virtual bool visitDeclaration(Declaration *decl)
  {
    if (decl->dflags & DF_EXTERN)
      return true;

    FakeList<Declarator> *decl_list = decl->decllist;
    while (decl_list != NULL) {
      Declarator *d = decl_list->first();
      decl_list = decl_list->butFirst();

      if (d->type->isFunctionType())
        continue;

      if (d->var->hasFlag(DF_STATIC | DF_GLOBAL))
        continue;

      benv->local_table.Insert(d->var->name, d->var);
    }

    return true;
  }
};

// peel off declarator modifiers until we get to an underlying
// array, then get its size. i.e. int *x[10] -> 10.
// we need this because ArrayType does not remember how large
// dynamically sized arrays are.
Expression* GetArraySize(IDeclarator *idecl)
{
  switch (idecl->kind()) {

  case IDeclarator::D_ARRAY:
    return idecl->asD_array()->size;

  case IDeclarator::D_POINTER:
    return GetArraySize(idecl->asD_pointer()->base);
  case IDeclarator::D_FUNC:
    return GetArraySize(idecl->asD_func()->base);
  case IDeclarator::D_GROUPING:
    return GetArraySize(idecl->asD_grouping()->base);

  default:
    return NULL;

  }
}

void ProcessDeclarator(PPoint *cur_point, Declarator *decl)
{
  // insert a call to alloca for dynamically sized arrays.
  if (decl->var->type->isArrayType()) {
    ArrayType *arr = decl->var->type->asArrayType();
    if (arr->size == ArrayType::DYN_SIZE) {
      Expression *dyn_length = GetArraySize(decl->decl);
      Assert(dyn_length);

      Xgill::Variable *var = GetVariable(decl->var);
      Xgill::Exp *var_exp = Xgill::Exp::MakeVar(var);

      Xgill::Exp *length_value;
      ExprEnv length_expr_env(cur_point);
      length_expr_env.result_rval = &length_value;
      ProcessExpression(length_expr_env, dyn_length);

      Type *single_type = decl->var->type->asArrayType()->eltType;
      int single_type_size;
      benv->base_env.sizeofType(single_type, single_type_size, NULL);

      // get an expression for length * sizeof(elem_type)
      Xgill::Exp *size_arg = Xgill::Exp::MakeInt(single_type_size);
      size_arg =
        Xgill::Exp::MakeBinop(Xgill::B_Mult, size_arg, length_value, NULL,
                              POINTER_BITS, false);

      Xgill::Location *loc = benv->cfg->GetPointLocation(*cur_point);
      DoAllocateCall(loc, cur_point, "alloca", var_exp, size_arg);
    }
  }

  if (decl->ctorStatement != NULL)
    ProcessStatement(decl->ctorStatement, true, cur_point);

  // only do the initializer if it isn't a constructor. constructor
  // initializers are folded in with the ctorStatement.
  if (decl->init != NULL && !decl->init->isIN_ctor()) {
    Xgill::Variable *var = GetVariable(decl->var);
    Xgill::Exp *var_exp = Xgill::Exp::MakeVar(var);

    ProcessInitializer(cur_point, var_exp, decl->var->type, decl->init);
  }
}

// add any destructors to scope_env for the specified statement.
void ScopeAddDestructors(ScopeEnv &scope_env, Statement *stmt)
{
  if (S_decl *nstmt = stmt->ifS_decl()) {
    FakeList<Declarator> *decl_list = nstmt->decl->decllist;
    while (decl_list != NULL) {
      Declarator *d = decl_list->first();
      decl_list = decl_list->butFirst();

      if (d->dtorStatement != NULL)
        scope_env.destructors.PushBack(d->dtorStatement);
    }
  }
}

void InitializeScope(ScopeEnv &scope_env, Statement *stmt)
{
  scope_env.stmt = stmt;

  // add any destructors for the statement's declarations.
  if (S_compound *nstmt = stmt->ifS_compound()) {
    for (int ind = 0; ind < nstmt->stmts.count(); ind++) {
      Statement *child_stmt = nstmt->stmts.nth(ind);
      ScopeAddDestructors(scope_env, child_stmt);
    }
  }
  else {
    ScopeAddDestructors(scope_env, stmt);
  }
}

void ProcessExitScope(const ScopeEnv &scope_env,
                      PPoint *cur_point)
{
  for (size_t dind = 0; dind < scope_env.destructors.Size(); dind++) {
    Statement *dtor = scope_env.destructors[dind];
    ProcessStatement(dtor, true, cur_point);
  }
}

// process the specified statement, but wrap a new scope around its execution.
void ProcessStatementWrapScope(Statement *stmt, PPoint *cur_point,
                               PPoint break_point = 0,
                               PPoint continue_point = 0,
                               Xgill::Exp *switch_value = NULL,
                               PPoint *switch_point = NULL,
                               PPoint *default_point = NULL)
{
  benv->scopes.PushBack(ScopeEnv());
  ScopeEnv &scope_env = benv->scopes.Back();
  scope_env.break_point = break_point;
  scope_env.continue_point = continue_point;
  scope_env.switch_value = switch_value;
  scope_env.switch_point = switch_point;
  scope_env.default_point = default_point;
  InitializeScope(scope_env, stmt);

  ProcessStatement(stmt, false, cur_point);

  ScopeEnv &back_scope_env = benv->scopes.Back();
  ProcessExitScope(back_scope_env, cur_point);
  benv->scopes.PopBack();
}

// gets the scope for the innermost switch statement at the current point
// of execution, or NULL if there is no switch scope.
const ScopeEnv* GetInnerSwitchScope()
{
  for (ssize_t sind = benv->scopes.Size() - 1; sind >= 0; sind--) {
    const ScopeEnv &scope_env = benv->scopes[sind];
    if (scope_env.switch_value != NULL) {
      Assert(scope_env.switch_point != NULL);
      Assert(scope_env.default_point != NULL);
      return &scope_env;
    }
  }
  return NULL;
}

void ProcessStatement(Statement *stmt, bool new_scope,
                      PPoint *cur_point)
{
  Assert(stmt);

  // update the location of the entry point to this statement.
  Xgill::Location *loc = GetLocation(stmt->loc);
  benv->cfg->SetPointLocation(*cur_point, loc);

  // get an extra reference on the statement. the reference we just
  // transferred to the CFG might go away if another statement picks
  // a new location for the same point.
  loc->IncRef(stmt);

  switch (stmt->kind()) {

  // nop statements.
  case Statement::S_SKIP:
  case Statement::S_NAMESPACEDECL:
  case Statement::S_FUNCTION:
    break;

  case Statement::S_LABEL: {
    S_label *nstmt = stmt->asS_label();

    // we need to link in the point assigned to this label.
    bool found_label = false;
    for (size_t lind = 0; lind < benv->labels.Size(); lind++) {
      const LabelData &data = benv->labels[lind];
      if (data.label == nstmt) {
        found_label = true;
        AddSkipEdge(*cur_point, data.point);
        *cur_point = data.point;
        break;
      }
    }

    ProcessStatement(nstmt->s, true, cur_point);
    break;
  }

  case Statement::S_CASE:
  case Statement::S_RANGECASE: {
    const ScopeEnv *scope = GetInnerSwitchScope();
    Assert(scope);

    // we need the body statement to execute and the condition to test
    // at switch entry to see if we branch here.
    Statement *child_stmt = NULL;
    Xgill::Exp *cond_test = NULL;

    if (S_case *nstmt = stmt->ifS_case()) {
      child_stmt = nstmt->s;

      int case_value;  // TODO: fix stupid limit on size of value.
      if (nstmt->expr->constEval(benv->base_env, case_value)) {
        Xgill::Exp *case_exp = Xgill::Exp::MakeInt(case_value);

        scope->switch_value->IncRef();
        cond_test = Xgill::Exp::MakeBinop(Xgill::B_Equal,
                                          scope->switch_value, case_exp);
      }
    }
    else if (S_rangeCase *nstmt = stmt->ifS_rangeCase()) {
      child_stmt = nstmt->s;

      int low_case_value;
      int high_case_value;
      if (nstmt->exprLo->constEval(benv->base_env, low_case_value) &&
          nstmt->exprHi->constEval(benv->base_env, high_case_value)) {
        Xgill::Exp *low_exp = Xgill::Exp::MakeInt(low_case_value);
        Xgill::Exp *high_exp = Xgill::Exp::MakeInt(high_case_value);

        scope->switch_value->IncRef();
        Xgill::Exp *low_test =
          Xgill::Exp::MakeBinop(Xgill::B_GreaterEqual,
                                scope->switch_value, low_exp);

        scope->switch_value->IncRef();
        Xgill::Exp *high_test =
          Xgill::Exp::MakeBinop(Xgill::B_LessEqual,
                                scope->switch_value, high_exp);

        cond_test =
          Xgill::Exp::MakeBinop(Xgill::B_LogicalAnd, low_test, high_test);
      }
    }
    else {
      Assert(false);
    }

    if (cond_test) {
      cond_test->IncRef();  // need references for both edges.

      // point to fall through at switch entry if the test is not met.
      loc->IncRef();
      PPoint after_point = benv->cfg->AddPoint(loc);

      // fix the point for the source of the edges to the location
      // of this case, not the previous case.
      loc->IncRef();
      benv->cfg->SetPointLocation(*scope->switch_point, loc);

      Xgill::PEdge *true_edge =
        Xgill::PEdge::MakeAssume(*scope->switch_point, *cur_point,
                                 cond_test, true);
      Xgill::PEdge *false_edge =
        Xgill::PEdge::MakeAssume(*scope->switch_point, after_point,
                                 cond_test, false);

      benv->cfg->AddEdge(true_edge);
      benv->cfg->AddEdge(false_edge);

      *scope->switch_point = after_point;
    }
    else {
      ProcessFailure("ProcessStatement(): S_CASE / S_RANGECASE");
    }

    Assert(child_stmt);
    ProcessStatement(child_stmt, true, cur_point);
    break;
  }

  case Statement::S_DEFAULT: {
    S_default *nstmt = stmt->asS_default();

    const ScopeEnv *scope = GetInnerSwitchScope();
    Assert(scope);

    Assert(*scope->default_point == 0);
    *scope->default_point = *cur_point;

    ProcessStatement(nstmt->s, true, cur_point);
    break;
  }

  case Statement::S_EXPR: {
    S_expr *nstmt = stmt->asS_expr();

    ExprEnv expr_env(cur_point);
    ProcessExpression(expr_env, nstmt->expr->expr);
    break;
  }

  case Statement::S_COMPOUND: {
    S_compound *nstmt = stmt->asS_compound();

    if (new_scope) {
      ProcessStatementWrapScope(stmt, cur_point);
    }
    else {
      for (int ind = 0; ind < nstmt->stmts.count(); ind++) {
        Statement *child_stmt = nstmt->stmts.nth(ind);
        ProcessStatement(child_stmt, true, cur_point);
      }
    }

    break;
  }

  case Statement::S_IF: {
    S_if *nstmt = stmt->asS_if();

    loc->IncRef();
    PPoint true_point = benv->cfg->AddPoint(loc);

    loc->IncRef();
    PPoint false_point = benv->cfg->AddPoint(loc);

    ProcessConditionBranch(cur_point, true_point, false_point, nstmt->cond);

    ProcessStatementWrapScope(nstmt->thenBranch, &true_point);
    ProcessStatementWrapScope(nstmt->elseBranch, &false_point);

    loc->IncRef();
    PPoint join_point = benv->cfg->AddPoint(loc);

    AddSkipEdge(true_point, join_point);
    AddSkipEdge(false_point, join_point);
    *cur_point = join_point;
    break;
  }

  case Statement::S_WHILE: {
    S_while *nstmt = stmt->asS_while();

    PPoint entry_point = *cur_point;
    Xgill::Location *end_loc = GetLocation(stmt->end_loc);

    benv->cfg->AddLoopHead(entry_point, end_loc);

    loc->IncRef();
    PPoint break_point = benv->cfg->AddPoint(loc);

    loc->IncRef();
    PPoint body_point = benv->cfg->AddPoint(loc);

    ProcessConditionBranch(cur_point, body_point, break_point, nstmt->cond);

    ProcessStatementWrapScope(nstmt->body, &body_point,
                              break_point, entry_point);
    AddSkipEdge(body_point, entry_point);

    *cur_point = break_point;
    break;
  }

  case Statement::S_DOWHILE: {
    S_doWhile *nstmt = stmt->asS_doWhile();

    PPoint entry_point = *cur_point;
    Xgill::Location *end_loc = GetLocation(stmt->end_loc);

    benv->cfg->AddLoopHead(entry_point, end_loc);

    loc->IncRef();
    PPoint break_point = benv->cfg->AddPoint(loc);

    // point for before the while expression. this is where 'continue' goes.
    loc->IncRef();
    PPoint after_point = benv->cfg->AddPoint(loc);

    ProcessStatementWrapScope(nstmt->body, cur_point,
                              break_point, after_point);
    AddSkipEdge(*cur_point, after_point);

    ExprEnv expr_env(&after_point);
    expr_env.SetResultBranch(entry_point, break_point);
    ProcessExpression(expr_env, nstmt->expr->expr);

    *cur_point = break_point;
    break;
  }

  case Statement::S_FOR: {
    S_for *nstmt = stmt->asS_for();

    PPoint exit_init = *cur_point;
    ProcessStatement(nstmt->init, true, &exit_init);

    Xgill::Location *end_loc = GetLocation(stmt->end_loc);

    benv->cfg->AddLoopHead(exit_init, end_loc);

    loc->IncRef();
    PPoint break_point = benv->cfg->AddPoint(loc);

    loc->IncRef();
    PPoint body_point = benv->cfg->AddPoint(loc);

    PPoint pre_cond_point = exit_init;
    ProcessConditionBranch(&pre_cond_point, body_point, break_point, nstmt->cond);

    // point for before the after expression. this is where 'continue' goes.
    loc->IncRef();
    PPoint after_point = benv->cfg->AddPoint(loc);

    ProcessStatementWrapScope(nstmt->body, &body_point,
                              break_point, after_point);
    AddSkipEdge(body_point, after_point);

    ExprEnv expr_env(&after_point);
    ProcessExpression(expr_env, nstmt->after->expr);
    AddSkipEdge(after_point, exit_init);

    *cur_point = break_point;
    break;
  }

  case Statement::S_RETURN: {
    S_return *nstmt = stmt->asS_return();

    Xgill::Variable *ret_var =
      Xgill::Variable::Make(benv->GetVariableId(), Xgill::VK_Return,
                            NULL, 0, NULL);

    Assert(benv->func);
    Type *retType = benv->func->funcType->retType;

    if (!retType->isVoid()) {
      ret_var->IncRef();
      benv->cfg->AddVariable(ret_var, GetType(retType));
    }

    Xgill::Exp *ret_lval = Xgill::Exp::MakeVar(ret_var);

    if (nstmt->ctorStatement) {
      Assert(nstmt->expr && !nstmt->expr->expr);

      // return by value of a compound type.
      Expression *ctorExpr = nstmt->ctorStatement->asS_expr()->expr->expr;
      ExprEnv ctor_expr_env(cur_point);
      ctor_expr_env.ctor_instance_lval = ret_lval;
      ProcessExpression(ctor_expr_env, ctorExpr);
    }
    else if (nstmt->expr && nstmt->expr->expr) {
      // return of a pointer or other non-compound value.
      ExprEnv expr_env(cur_point);
      expr_env.SetResultAssign(ret_lval,
                               retType->asRval(),
                               retType->isReference());
      ProcessExpression(expr_env, nstmt->expr->expr);
    }
    else {
      // don't need the return lvalue.
      ret_lval->DecRef();
    }

    // jump to function exit and execute destructors for all containing scopes.
    for (ssize_t sind = benv->scopes.Size() - 1; sind >= 0; sind--)
      ProcessExitScope(benv->scopes[sind], cur_point);
    AddSkipEdge(*cur_point, benv->cfg->GetExitPoint());

    // unreachable point for the fall through.
    loc->IncRef();
    *cur_point = benv->cfg->AddPoint(loc);
    break;
  }

  case Statement::S_DECL: {
    S_decl *nstmt = stmt->asS_decl();

    if (nstmt->decl->dflags & DF_EXTERN)
      break;

    FakeList<Declarator> *decl_list = nstmt->decl->decllist;
    while (decl_list != NULL) {
      Declarator *d = decl_list->first();
      decl_list = decl_list->butFirst();

      if (d->type->isFunctionType())
        continue;

      // don't run the initializers for any static variables.
      // these are handled as global initializers.
      if (d->var->hasFlag(DF_STATIC))
        continue;

      // we shouldn't see any global variables here.
      Assert(!d->var->hasFlag(DF_GLOBAL));

      ProcessDeclarator(cur_point, d);
    }

    break;
  }

  case Statement::S_ASM: {
    loc->IncRef();
    PPoint after_point = benv->cfg->AddPoint(loc);

    Xgill::PEdge *asm_edge =
      Xgill::PEdge::MakeAssembly(*cur_point, after_point);
    benv->cfg->AddEdge(asm_edge);

    *cur_point = after_point;
    break;
  }

  case Statement::S_BREAK:
  case Statement::S_CONTINUE: {
    bool found_point = false;
    for (ssize_t sind = benv->scopes.Size() - 1; sind >= 0; sind--) {
      const ScopeEnv &scope_env = benv->scopes[sind];

      PPoint jump_point =
        (stmt->kind() == Statement::S_BREAK)
        ? scope_env.break_point
        : scope_env.continue_point;

      if (jump_point != 0) {
        found_point = true;

        // pop scopes up to and including the one containing the break/continue.
        for (ssize_t xsind = benv->scopes.Size() - 1; xsind >= sind; xsind--)
          ProcessExitScope(benv->scopes[xsind], cur_point);

        AddSkipEdge(*cur_point, jump_point);
        break;
      }
    }
    Assert(found_point);

    // unreachable point for the fall through.
    loc->IncRef();
    *cur_point = benv->cfg->AddPoint(loc);
    break;
  }

  case Statement::S_GOTO: {
    S_goto *nstmt = stmt->asS_goto();

    bool found_label = false;
    for (size_t lind = 0; lind < benv->labels.Size(); lind++) {
      const LabelData &data = benv->labels[lind];

      if (strcmp(data.label->name, nstmt->target) == 0) {
        found_label = true;

        // the point for this label is a potential loop head.
        benv->cfg->AddLoopHead(data.point, NULL);

        // find the tightest scope which contains both the goto
        // and label statements, and run the destructors for any
        // scopes which the goto jumped out of.
        bool found_scope = false;
        for (ssize_t sind = benv->scopes.Size() - 1; sind >= 0; sind--) {
          const ScopeEnv &scope_env = benv->scopes[sind];

          bool contains_label = false;
          for (size_t lsind = 0; lsind < data.stmt_list.Size(); lsind++) {
            if (scope_env.stmt == data.stmt_list[lsind]) {
              contains_label = true;
              break;
            }
          }

          if (contains_label) {
            found_scope = true;

            // pop scopes up to but excluding the one containing the label.
            for (ssize_t xsind = benv->scopes.Size() - 1; xsind > sind; xsind--)
              ProcessExitScope(benv->scopes[xsind], cur_point);

            AddSkipEdge(*cur_point, data.point);
            break;
          }
        }
        Assert(found_scope);

        break;
      }
    }
    Assert(found_label);

    // unreachable point for the fall through.
    loc->IncRef();
    *cur_point = benv->cfg->AddPoint(loc);
    break;
  }

  case Statement::S_SWITCH: {
    S_switch *nstmt = stmt->asS_switch();

    Xgill::Exp *cond_value;
    ExprEnv cond_expr_env(cur_point);
    cond_expr_env.result_rval = &cond_value;
    ProcessCondition(cond_expr_env, nstmt->cond);

    // assign switched value to a temporary unless it is already an lvalue.
    if (!cond_value->IsLvalue()) {
      Xgill::Type *temp_type = Xgill::Type::MakeInt(POINTER_BITS / 8, true);
      Xgill::Exp *temp_exp = GetNewTemporary(temp_type);
      temp_exp->IncRef();

      // point for after the assignment.
      loc->IncRef();
      PPoint after_point = benv->cfg->AddPoint(loc);

      temp_type->IncRef();
      Xgill::PEdge *temp_edge =
        Xgill::PEdge::MakeAssign(*cur_point, after_point,
                                 temp_type, temp_exp, cond_value);
      benv->cfg->AddEdge(temp_edge);

      cond_value = Xgill::Exp::MakeDrf(temp_exp);
      *cur_point = after_point;
    }

    cond_value->MoveRef(NULL, stmt);

    // entry point of the switch body.
    loc->IncRef();
    PPoint body_point = benv->cfg->AddPoint(loc);

    // point to jump for break statements.
    loc->IncRef();
    PPoint break_point = benv->cfg->AddPoint(loc);

    // point which will receive the target of the 'default' label if it exists.
    PPoint default_point = 0;

    // process the switch body and add the appropriate tests for each case
    // after cur_point.
    ProcessStatementWrapScope(nstmt->branches, &body_point,
                              break_point, 0,
                              cond_value, cur_point, &default_point);

    if (default_point != 0) {
      // fall through after testing the cases to the 'default' label.
      AddSkipEdge(*cur_point, default_point);
    }
    else {
      // fall through the switch if there is no 'default' and no cases match.
      AddSkipEdge(*cur_point, break_point);
    }

    // the switch body falls through to the break point.
    AddSkipEdge(body_point, break_point);

    cond_value->DecRef(stmt);
    *cur_point = break_point;
    break;
  }

  // INCOMPLETE
  case Statement::S_TRY: {
    S_try *nstmt = stmt->asS_try();

    // we are not yet modeling exception handling so there are no
    // edges from anywhere to the exception handlers.
    ProcessStatementWrapScope(nstmt->body, cur_point);
    break;
  }

  // INCOMPLETE
  case Statement::S_COMPUTEDGOTO: {
    // punt on computed gotos. make an edge to terminate the program.
    AddSkipEdge(*cur_point, 0);

    // unreachable point for the fall through.
    loc->IncRef();
    *cur_point = benv->cfg->AddPoint(loc);
    break;
  }

  default:
    Assert(false);
  }

  loc->DecRef(stmt);
}

void ProcessFunctionBody(Function *func)
{
  PPoint cur_point = benv->cfg->GetEntryPoint();
  Assert(cur_point);

  FakeList <MemberInit>* init_list = func->inits;

  // the return variable is normally the object being constructed.
  // this can be NULL if Elsa got deeply confused by parse/tcheck errors
  // and made a constructor where it didn't know what it was constructing.
  if (init_list && func->retVar) {
    // Elsa seems to be inserting default constructors for members or
    // base classes not explicitly mentioned in the initializers list.

    Assert(func->retVar->type->isReference());

    Xgill::Variable *this_var =
      Xgill::Variable::Make(benv->GetVariableId(), Xgill::VK_This,
                            NULL, 0, NULL);

    this_var->IncRef();
    benv->cfg->AddVariable(this_var, GetType(func->retVar->type));

    Xgill::Exp *this_exp = Xgill::Exp::MakeVar(this_var);
    Xgill::Exp *this_drf = Xgill::Exp::MakeDrf(this_exp);

    while (init_list != NULL) {
      MemberInit *init = init_list->first();
      init_list = init_list->butFirst();

      if (init->base != NULL) {
        if (init->ctorStatement != NULL) {
          this_drf->IncRef();
          Expression *ctorExpr = init->ctorStatement->asS_expr()->expr->expr;
          ExprEnv ctor_expr_env(&cur_point);
          ctor_expr_env.ctor_instance_lval = this_drf;
          ProcessExpression(ctor_expr_env, ctorExpr);
        }
        else {
          // this will only come up when the base class uses a builtin
          // constructor which does not initialize any fields.
        }
      }
      else if (init->ctorStatement != NULL) {
        ProcessStatement(init->ctorStatement, false, &cur_point);
      }
      else if (init->args->count() == 1) {
        Assert(init->member != NULL);

        this_drf->IncRef();
        Xgill::Field *field = GetVariableField(init->member);
        Xgill::Exp *field_exp = Xgill::Exp::MakeFld(this_drf, field);

        Type *init_type = init->member->type;

        ExprEnv expr_env(&cur_point);
        expr_env.SetResultAssign(field_exp,
                                 init_type->asRval(),
                                 init_type->isReference());
        ProcessExpression(expr_env, init->args->first()->expr);
      }
    }

    this_drf->DecRef();
  }

  Statement *stmt = func->body;

  // prepass over the function body to collect label and local variable info.
  XgillBodyVisitor visitor;
  stmt->traverse(visitor);

  benv->scopes.PushBack(ScopeEnv());
  ScopeEnv &scope_env = benv->scopes.Back();
  InitializeScope(scope_env, stmt);

  ProcessStatement(stmt, false, &cur_point);

  ScopeEnv &back_scope_env = benv->scopes.Back();
  ProcessExitScope(back_scope_env, &cur_point);
  benv->scopes.PopBack();

  AddSkipEdge(cur_point, benv->cfg->GetExitPoint());
}
