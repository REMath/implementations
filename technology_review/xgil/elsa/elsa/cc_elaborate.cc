// cc_elaborate.cc            see license.txt for copyright and terms of use
// code for cc_elaborate.h


// Subtree cloning strategy (SCS):
//
// Since cloning remains somewhat ad-hoc and untested, when a node has
// subtrees that are used in its elaboration, we clone the subtrees
// but put the clone back into the subtree pointer.  Then the original
// subtree (trusted to be properly tcheck'd) is what's used in the
// elaboration, since we assume that analyses will look at the
// elaboration to the exclusion of the subtree pointer.
//
// Update: The problem with this is that an analysis has to be
// explicitly coded to avoid the cloned, defunct subtrees, otherwise
// it encounters un-elaborated AST.  Therefore the new default is to
// simply nullify defunct subtrees, despite the fact that it
// technically results in invalid AST (e.g. E_delete with a NULL
// 'expr').  The analysis can request the full SCS by setting
// 'ElabVisitor::cloneDefunct' to true.


// Subtree elaboration strategy (SES):
//
// Q: An AST node may have subtrees.  When do the subtrees get
// elaborated, with respect to the elaboration of the parent node?
//
// A: The parent node's elaborate() function (goes by various names
// in the following code) is called first.  The parent then has the
// responsibility of elaborating its children manually.  For example,
// if it puts its children into a ctorStatement, 'makeCtorStatement'
// will elaborate the arguments (children).  Then the visitor returns
// 'false' so that the children are not elaborated again.  (In fact
// it would be the children's clones being elaborated "again", and I
// don't want to elaborate clones.)


#include "cc_elaborate.h"      // this module
#include "cc_ast.h"            // Declaration
#include "ast_build.h"         // makeExprList1, etc.
#include "trace.h"             // TRACE
#include "cc_print.h"          // PrintEnv
                                                        
// cc_type.h
Type *makeLvalType(TypeFactory &tfac, Type *underlying);


// --------------------- ElabVisitor misc. ----------------------
ElabVisitor::ElabVisitor(StringTable &s, TypeFactory &tf,
                         TranslationUnit *tu)
  : loweredVisitor(this, VF_NONE),
    str(s),
    tfac(tf),
    tunit(tu),
    env(*this),
    functionStack(),              // empty
    fullExpressionAnnotStack(),   // empty
    enclosingStmtLoc(SL_UNKNOWN),
    receiverName(s("__receiver")),
    activities(EA_ALL),
    cloneDefunctChildren(false),
    tempSerialNumber(0),
    e_newSerialNumber(0)
{}

ElabVisitor::~ElabVisitor()
{}


StringRef ElabVisitor::makeTempName()
{
  return str(stringc << "temp-name-" << tempSerialNumber++);
}

StringRef ElabVisitor::makeE_newVarName()
{
  return str(stringc << "e_new-name-" << e_newSerialNumber++);
}

StringRef ElabVisitor::makeThrowClauseVarName()
{
  return str(stringc << "throwClause-name-" << throwClauseSerialNumber++);
}

StringRef ElabVisitor::makeCatchClauseVarName()
{
  return str(stringc << "catchClause-name-" << throwClauseSerialNumber++);
}


Variable *ElabVisitor::makeVariable(SourceLoc loc, StringRef name,
                                    Type *type, DeclFlags dflags)
{
  return tfac.makeVariable(loc, name, type, dflags, tunit /*doh!*/);
}


// ----------------------- AST creation ---------------------------
// This section contains functions that build properly-tcheck'd
// AST nodes of a variety of kinds.  Part of the strategy for
// building tcheck'd nodes is for most of the elaboration code
// to use the functions in this section, which are then individually
// checked to ensure they set all the fields properly, instead of
// building AST nodes from scratch.


// Variable -> D_name
D_name *ElabVisitor::makeD_name(SourceLoc loc, Variable *var)
{
  D_name *ret = new D_name(loc, new PQ_variable(loc, var));
  return ret;
}


// given a Variable, make a Declarator that refers to it; assume it's
// being preceded by a TS_name that fully specifies the variable's
// type, so we just use a D_name to finish it off
Declarator *ElabVisitor::makeDeclarator(SourceLoc loc, Variable *var)
{
  IDeclarator *idecl = makeD_name(loc, var);

  Declarator *decl = new Declarator(idecl, NULL /*init*/);
  decl->var = var;
  decl->type = var->type;

  return decl;
}

// and similar for a full (singleton) declaration
Declaration *ElabVisitor::makeDeclaration(SourceLoc loc, Variable *var)
{
  Declarator *declarator = makeDeclarator(loc, var);
  Declaration *declaration =
    new Declaration(DF_NONE, new TS_type(loc, loc, var->type),
      FakeList<Declarator>::makeList(declarator));
  return declaration;
}


// given a function declaration, make a Declarator containing
// a D_func that refers to it
Declarator *ElabVisitor::makeFuncDeclarator(SourceLoc loc, Variable *var)
{
  FunctionType *ft = var->type->asFunctionType();

  // construct parameter list
  FakeList<ASTTypeId> *params = FakeList<ASTTypeId>::emptyList();
  {
    // iterate over parameters other than the receiver object ("this")
    SObjListIterNC<Variable> iter(ft->params);
    if (ft->isMethod()) {
      iter.adv();
    }
    for (; !iter.isDone(); iter.adv()) {
      Variable *param = iter.data();

      ASTTypeId *typeId = new ASTTypeId(new TS_type(loc, loc, param->type),
                                        makeDeclarator(loc, param));
      params = params->prepend(typeId);
    }
    params = params->reverse();     // fix prepend()-induced reversal
  }

  // build D_func
  IDeclarator *funcIDecl = new D_func(loc,
                                      makeD_name(loc, var),
                                      params,
                                      CV_NONE,
                                      NULL /*exnSpec*/);

  Declarator *funcDecl = new Declarator(funcIDecl, NULL /*init*/);
  funcDecl->var = var;
  funcDecl->type = var->type;

  return funcDecl;
}


// given a function declaration and a body, make a Function AST node
Function *ElabVisitor::makeFunction(SourceLoc loc, Variable *var, 
                                    FakeList<MemberInit> *inits,
                                    S_compound *body)
{
  FunctionType *ft = var->type->asFunctionType();

  Declarator *funcDecl = makeFuncDeclarator(loc, var);

  Function *f = new Function(
    var->flags        // this is too many (I only want syntactic); but won't hurt
      | DF_INLINE,    // pacify pretty-printing idempotency
    new TS_type(loc, loc, ft->retType),
    funcDecl,
    inits,
    body,
    NULL /*handlers*/
  );
  f->funcType = var->type->asFunctionType();

  if (ft->isMethod()) {
    // f's receiver should match that of its funcType
    f->receiver = f->funcType->getReceiver();
  }

  f->implicitlyDefined = true;

  // the existence of a definition has implications for the Variable too
  var->setFlag(DF_DEFINITION);
  var->funcDefn = f;

  return f;
}


// given a Variable, make an E_variable referring to it
E_variable *ElabVisitor::makeE_variable(SourceLoc loc, Variable *var)
{
  E_variable *evar = new E_variable(new PQ_variable(loc, var));
  evar->type = makeLvalType(tfac, var->type);
  evar->var = var;
  return evar;
}

E_fieldAcc *ElabVisitor::makeE_fieldAcc
  (SourceLoc loc, Expression *obj, Variable *field)
{
  E_fieldAcc *efieldacc = new E_fieldAcc(obj, new PQ_variable(loc, field));
  efieldacc->type = makeLvalType(tfac, field->type);
  efieldacc->field = field;
  return efieldacc;
}


E_funCall *ElabVisitor::makeMemberCall
  (SourceLoc loc, Expression *obj, Variable *func, FakeList<ArgExpression> *args)
{
  // "a.f"
  E_fieldAcc *efieldacc = makeE_fieldAcc(loc, obj, func);

  // "a.f(<args>)"
  E_funCall *funcall = new E_funCall(efieldacc, args);
  funcall->type = func->type->asFunctionType()->retType;

  return funcall;
}

FakeList<ArgExpression> *ElabVisitor::emptyArgs()
{
  return FakeList<ArgExpression>::emptyList();
}

          
// reference to the receiver object of the current function
Expression *ElabVisitor::makeThisRef(SourceLoc loc)
{
  Variable *receiver = functionStack.top()->receiver;

  // "this"
  E_this *ths = new E_this;
  ths->receiver = receiver;
  ths->type = tfac.makePointerType(CV_CONST, receiver->type->asRval());

  // "*this"
  E_deref *deref = new E_deref(ths);
  deref->type = receiver->type;

  return deref;
}


// wrap up an expression in an S_expr
S_expr *ElabVisitor::makeS_expr(SourceLoc loc, Expression *e)
{
  return new S_expr(loc, loc, new FullExpression(e));
}


// make an empty S_compound
S_compound *ElabVisitor::makeS_compound(SourceLoc loc)
{
  // note that the ASTList object created here is *deleted* by
  // the act of passing it to the S_compound; the S_compound has
  // its own ASTList<Statement> inside it
  return new S_compound(loc, loc, new ASTList<Statement>);
}


// ------------------------ makeCtor ----------------------
// Make a call to the constructor for 'type', such that the object
// constructed is in 'target' (a reference to some memory location).
// 'args' is the list of arguments to the ctor call.
E_constructor *ElabVisitor::makeCtorExpr(
  SourceLoc loc,                    // where elaboration is occurring
  Expression *target,               // reference to object to construct
  Type *type,                       // type of the constructed object
  Variable *ctor,                   // ctor function to call
  FakeList<ArgExpression> *args)    // arguments to ctor (tcheck'd)
{
  xassert(target->type->isReference());

  E_constructor *ector0 = new E_constructor(new TS_type(loc, loc, type), args);
  ector0->type = type;
  ector0->ctorVar = ctor;
  ector0->artificial = true;
  ector0->retObj = target;

  // want to return a node that is both tcheck'd *and* elaborated
  ector0->traverse(this->loweredVisitor);

  return ector0;
}

// NOTE: the client should consider cloning the _args_ before passing
// them in so that the AST remains a tree
Statement *ElabVisitor::makeCtorStatement(
  SourceLoc loc,
  Expression *target,
  Type *type,
  Variable *ctor,
  FakeList<ArgExpression> *args)
{
  // see comment below regarding 'getDefaultCtor'; if this assertion
  // fails it may be due to an input program that is not valid C++,
  // but the type checker failed to diagnose it
  //xassert(ctor);

  if (ctor && !ctor->isBuiltin) {
    // non-builtin constructor, make an explicit call.
    E_constructor *ector0 = makeCtorExpr(loc, target, type, ctor, args);
    Statement *ctorStmt0 = makeS_expr(loc, ector0);
    return ctorStmt0;
  }
  else if (ctor && ctor->isBuiltinCopy) {
    // builtin copy constructor. inline a copy for all structure fields.
    xassert(ctor->scope && ctor->scope->curCompound);

    xassert(args->count() == 1);
    Expression *arg = args->first()->expr;

    Expression *action = new E_assign(target, BIN_ASSIGN, arg);
    action->type = ctor->scope->curCompound->typedefVar->type;
    xassert(action->type);

    Statement *ctorStmt0 = makeS_expr(loc, action);
    return ctorStmt0;
  }
  else {
    // builtin default constructor. leaves everything uninitialized.
    return NULL;
  }
}


// ------------------------ makeDtor ----------------------
Expression *ElabVisitor::makeDtorExpr(SourceLoc loc, Expression *target,
                                      Type *type)
{
  Variable *dtor = getDtor(str, type->asCompoundType());

  // make the dtor statement, but only if it is not builtin. the builtin
  // dtor is a nop.
  if (dtor && !dtor->isBuiltin) {
    // question of whether to elaborate returned value is moot, as
    // elaboration would do nothin anyway
    return makeMemberCall(loc, target, dtor, emptyArgs());
  }
  else {
    return NULL;
  }
}

// NOTE: consider cloning the target so that the AST remains a tree
Statement *ElabVisitor::makeDtorStatement(SourceLoc loc, Expression *target,
                                          Type *type)
{
  Expression *efc0 = makeDtorExpr(loc, target, type);
  if (efc0) {
    return makeS_expr(loc, efc0);
  }
  else {
    return NULL;
  }
}


// ------------------- cloning support (SCS) ------------------
FakeList<ArgExpression> *ElabVisitor::cloneExprList(FakeList<ArgExpression> *args0)
{
  FakeList<ArgExpression> *ret = FakeList<ArgExpression>::emptyList();

  if (cloneDefunctChildren) {
    FAKELIST_FOREACH(ArgExpression, args0, iter) {
      // clone the AST node
      ArgExpression *argExpr0 = iter->clone();
      // use the clone
      ret = ret->prepend(argExpr0);
    }
    return ret->reverse();
  }
  else {
    // empty defunct list
    return ret;
  }
}
            

Expression *ElabVisitor::cloneExpr(Expression *e)
{
  if (cloneDefunctChildren) {
    // clone the AST node
    Expression *expr0 = e->clone();
    // use the clone
    return expr0;
  }
  else {
    return NULL;
  }
}


// ------------------------ elaborateCDtors -----------------------
void ElabVisitor::elaborateCDtorsDeclaration(Declaration *decl)
{
  FAKELIST_FOREACH_NC(Declarator, decl->decllist, decliter) {
    decliter->elaborateCDtors(env, decl->dflags);
  }

  // the caller isn't going to automatically traverse into the
  // type specifier, so we must do it manually
  // (e.g. cc_qual's test/memberInit_cdtor1.cc.filter-good.cc fails otherwise)
  decl->spec->traverse(this->loweredVisitor);
}


// for EA_MEMBER_DECL_CDTOR and EA_VARIABLE_DECL_CDTOR
//
// Given a Declarator, annotate it with statements that construct and
// destruct the associated variable.
void Declarator::elaborateCDtors(ElabVisitor &env, DeclFlags dflags)
{
  // don't do anything if this is not data
  if (var->type->isFunctionType() ||
      var->hasFlag(DF_TYPEDEF)) {
    return;
  }

  // also don't do this for parameters
  if (var->hasFlag(DF_PARAMETER)) {
    return;
  }

  // don't bother unless it is a class-valued object
  if (!type->isCompoundType()) {
    // except that we still need to elaborate the initializer, and the
    // caller is *not* going to let the visitor do so automatically
    // (since that would violate the SES in the case that the type
    // *is* compound)
    if (init) {
      init->traverse(env.loweredVisitor);
    }

    return;
  }
  CompoundType *ct = type->asCompoundType();

  // this is a property of the variable, not the declaration
  bool isTemporary =   var->hasFlag(DF_TEMPORARY);
  // these are properties of the declaration and the variable and
  // should match
  //
  // sm: at least in t0318.cc, they do not; the Variable has the
  // correct info, whereas the declaration merely has what was
  // syntactically present and/or obvious
  bool isMember =      var->hasFlag(DF_MEMBER);
  // this used to check if the *var* had an extern flag, which is not
  // correct because if there is a later declaration in the file for
  // the same variable that is *not* extern then the flag DF_EXTERN
  // will be removed, which seems reasonable to me.  What we care
  // about here is if the *declaration* is extern.
  bool isExtern =      dflags & DF_EXTERN;
  // note that this assertion is not an equality
  if (var->hasFlag(DF_EXTERN)) {
    xassert(isExtern);
  }

  bool isAbstract = decl->isD_name() && !decl->asD_name()->name;
  SourceLoc loc = getLoc();

  if (init) {
    // sm: why this assertion?
    xassert(!isTemporary);

    // sm: and why this one too?
    xassert(!isAbstract);

    // get a list of (tcheck'd) arguments to pass to the ctor; we will
    // clone the existing arguments, and put the clone in where the
    // original ones were
    FakeList<ArgExpression> *args0 = NULL;

    // the arguments have not yet been elaborated, that will happen
    // during 'makeCtorStatement'; but we need a fullexp context
    // for it
    FullExpressionAnnot *fullexp = NULL;

    // constructor to call
    Variable *ctor = NULL;

    ASTSWITCH(Initializer, init) {
      ASTCASE(IN_ctor, inctor) {
        args0 = inctor->args;
        inctor->args = env.cloneExprList(inctor->args);

        fullexp = inctor->getAnnot();
        ctor = inctor->ctorVar;
      }
      ASTNEXT(IN_expr, inexpr) {
        // just call the copy ctor; FIX: this is questionable; we
        // haven't decided what should really happen for an IN_expr;
        // update: dsw: I'm sure that is right
        args0 = makeExprList1(inexpr->e);
        inexpr->e = env.cloneExpr(inexpr->e);

        fullexp = inexpr->getAnnot();
        ctor = getCopyCtor(env.str, ct);
      }
      ASTNEXT(IN_compound, incpd) {
        // just call the no-arg ctor; FIX: this is questionable; it
        // is undefined what should happen for an IN_compound since
        // it is a C99-ism.
        //
        // sm: No it isn't.. IN_compound is certainly part of C++.
        // I still don't know how to handle it, though.
        args0 = env.emptyArgs();

        fullexp = incpd->getAnnot(); // sm: not sure about this..
        ctor = getDefaultCtor(env.str, ct);
        
        // NOTE: 'getDefaultCtor' can return NULL, corresponding to a class
        // that has no default ctor.  However, it is the responsibility of
        // the type checker to diagnose this case.  Now, as it happens, our
        // tchecker does not do so right now; but nevertheless it would be
        // wrong to, say, emit an error message here.  Instead,
        // 'makeCtorStatement' simply asserts that it is non-NULL.
      }
      ASTENDCASED
    }

    env.push(fullexp);
    ctorStatement = env.makeCtorStatement(loc, env.makeE_variable(loc, var),
                                          type, ctor, args0);
    env.pop(fullexp);
  }

  else /* init is NULL */ {
    if (!isAbstract &&
        !isTemporary &&
        !isMember &&
        !isExtern
        ) {                               
      // sm: I think this should not be reachable because I modified
      // the type checker to insert an IN_ctor in this case.  It would be
      // be bad if it *were* reachable, because there's no fullexp here.
      xfailure("should not be reachable");

      // call the no-arg ctor; for temporaries do nothing since this is
      // a temporary, it will be initialized later
      ctorStatement = env.makeCtorStatement(loc, env.makeE_variable(loc, var),
                                            type, getDefaultCtor(env.str, ct),
                                            env.emptyArgs());
    }
  }

  // make the dtorStatement
  if (!isAbstract &&
      !isExtern
      ) {
    // no need to clone the target as makeE_variable makes all new AST
    dtorStatement = env.makeDtorStatement(loc, env.makeE_variable(loc, var), type);
  } else {
    //xassert(!dtorStatement);
  }
}


// -------------------- elaborateCallSite ---------------------
// If the return type is a CompoundType, then make a temporary and
// point the retObj at it.  The intended semantics of this is to
// override the usual way of analyzing the return value just from the
// return type of the function.
//
// Make a Declaration for a temporary; yield the Variable too.
Declaration *ElabVisitor::makeTempDeclaration
  (SourceLoc loc, Type *retType, Variable *&var /*OUT*/)
{
  // while a user may attempt this, we should catch it earlier and not
  // end up down here.
  xassert(retType->isCompoundType());

  // make up a Variable
  var = makeVariable(loc, makeTempName(), retType, DF_TEMPORARY);

  // make a decl for it
  Declaration *decl = makeDeclaration(loc, var);

  // elaborate this declaration; because of DF_TEMPORARY this will *not*
  // add a ctor, but it will add a dtor
  elaborateCDtorsDeclaration(decl);

  return decl;
}

// make the decl, and add it to the innermost FullExpressionAnnot;
// yield the Variable since neither caller needs the Declaration
Variable *ElabVisitor::insertTempDeclaration(SourceLoc loc, Type *retType)
{
  FullExpressionAnnot *fea0 = env.fullExpressionAnnotStack.top();

  Variable *var;
  Declaration *declaration0 = makeTempDeclaration(loc, retType, var);

  // put it into fea0
  fea0->declarations.append(declaration0);

  return var;
}


// make a comma expression so we can copy the argument before passing it
//
// NOTE: the client is expected to clone _argExpr_ before passing it
// in here *if* needed, since we don't clone it below
Expression *ElabVisitor::elaborateCallByValue
  (SourceLoc loc, Type *paramType, Expression *argExpr)
{
  CompoundType *paramCt = paramType->asCompoundType();

  Variable *ctor = getCopyCtor(str, paramCt);
  if (!ctor || ctor->isBuiltin) {
    // the builtin copy constructor just copies over the fields,
    // so we do not need the extra temporary and can leave the argument alone.
    return argExpr;
  }

  // E_variable that points to the temporary
  Variable *tempVar = insertTempDeclaration(loc, paramType);

  // E_constructor for the temporary that calls the copy ctor for the
  // temporary taking the real argument as the copy ctor argument.
  // NOTE: we do NOT clone argExpr here, as the client to this
  // function is expected to do it
  E_constructor *ector =
    env.makeCtorExpr(loc, makeE_variable(loc, tempVar), paramType,
                     ctor, makeExprList1(argExpr));

  // combine into a comma expression so we do both but return the
  // value of the second
  //
  // sm: I choose to call 'makeE_variable' twice instead of using clone()
  // since I trust the former more
  Expression *byValueArg = makeE_variable(loc, tempVar);
  Expression *ret = new E_binary(ector, BIN_COMMA, byValueArg);
  ret->type = byValueArg->type;
  xassert(byValueArg->getType()->isReference()); // the whole point
  return ret;
}


// this returns the 'retObj', the object that the call is constructing
Expression *ElabVisitor::elaborateCallSite(
  SourceLoc loc,
  FunctionType *ft,
  FakeList<ArgExpression> *args,
  bool artificalCtor)          // always false; see call sites
{
  Expression *retObj = NULL;

  if (doing(EA_ELIM_RETURN_BY_VALUE)) {
    // If the return type is a CompoundType, then make a temporary and
    // point the retObj at it.  NOTE: This can never accidentally create
    // a temporary for a dtor for a non-temporary object because the
    // retType for a dtor is void.  However, we do need to guard against
    // this possibility for ctors.
    if (artificalCtor) {
      xassert(ft->isConstructor());
    }
    if (ft->retType->isCompoundType() &&
        (!ft->isConstructor() || !artificalCtor)   // sm: the isConstructor() test is redundant
        ) {
      Variable *var0 = insertTempDeclaration(loc, ft->retType);
      retObj = makeE_variable(loc, var0);
    }
  }

  if (doing(EA_ELIM_PASS_BY_VALUE)) {
    // Elaborate cdtors for CompoundType arguments being passed by
    // value.
    //
    // For each parameter, if it is a CompoundType (pass by value) then 1)
    // make a temporary variable here for it that has a dtor but not a
    // ctor 2) for the corresponding argument, replace it with a comma
    // expression where a) the first part is an E_constructor for the
    // temporary that has one argument that is what was the arugment in
    // this slot and the ctor is the copy ctor, and b) E_variable for the
    // temporary

    SObjListIterNC<Variable> paramsIter(ft->params);

    if (ft->isMethod()) {
      paramsIter.adv();
    }

    FAKELIST_FOREACH_NC(ArgExpression, args, arg) {
      if (paramsIter.isDone()) {
        // FIX: I suppose we could still have arguments here if there is a
        // ellipsis at the end of the parameter list.  Can those be passed
        // by value?
        break;
      }

      Variable *param = paramsIter.data();
      Type *paramType = param->getType();
      if (paramType->isCompoundType()) {
        // NOTE: it seems like this is one of those places where I
        // should NOT clone the "argument" argument to
        // makeCtorExpr/Statement (which is called by
        // elaborateCallByValue()) since it is being replaced by
        // something wrapped around itself: that is the AST tree remains
        // a tree
        //
        // sm: I agree
        arg->expr = elaborateCallByValue(loc, paramType, arg->expr);
      }

      paramsIter.adv();
    }

    if (!paramsIter.isDone()) {
      // FIX: if (!paramsIter.isDone()) then have to deal with default
      // arguments that are pass by value if such a thing is even
      // possible.
    }
  }

  return retObj;
}


// ----------------- elaborateFunctionStart -----------------
// for EA_ELIM_RETURN_BY_VALUE
void ElabVisitor::elaborateFunctionStart(Function *f)
{
  FunctionType *ft = f->funcType;
  if (ft->retType->isCompoundType()) {
    // We simulate return-by-value for class-valued objects by
    // passing a hidden additional parameter of type C& for a
    // return value of type C.  For static semantics, that means
    // adding an environment entry for a special name, "<retVar>".
    // For dynamic semantics, clients looking at the declaration
    // must simply know (by its name) that this variable is bound
    // to the reference passed as the 'retObj' at the call site.

    SourceLoc loc = f->nameAndParams->decl->loc;
    Type *retValType =
      env.tfac.makeReferenceType(ft->retType);
    StringRef retValName = env.str("<retVar>");
    f->retVar = env.makeVariable(loc, retValName, retValType, DF_PARAMETER);

    // sm: This seemed like a good idea, because an analysis would get
    // to see the declaration and not just the magical appearance of a
    // new Variable.  But, it was not present in the code that I'm
    // working from and it messes up pretty printing idempotency; and
    // I'm now not as convinced that an analysis really wants to see
    // it.  So I'm commenting it out.
    #if 0
    Declaration *declaration = makeDeclaration(loc, f->retVar);
    f->body->stmts.prepend(new S_decl(loc, declaration));
    #endif // 0
  }
}


// ---------------- completeNoArgMemberInits -------------------
// add no-arg MemberInits to existing ctor body ****************

// Does this Variable want a no-arg MemberInitializer?
bool ElabVisitor::wantsMemberInit(Variable *var) 
{
  // function members should be skipped
  if (var->type->isFunctionType()) return false;
  // skip arrays for now; FIX: do something correct here
  if (var->type->isArrayType()) return false;
  if (var->isStatic()) return false;
  if (var->hasFlag(DF_TYPEDEF)) return false;
  // FIX: do all this with one test
  xassert(!var->hasFlag(DF_AUTO));
  xassert(!var->hasFlag(DF_REGISTER));
  xassert(!var->hasFlag(DF_EXTERN));
  xassert(!var->hasFlag(DF_VIRTUAL)); // should be functions only
  xassert(!var->hasFlag(DF_EXPLICIT)); // should be ctors only
  xassert(!var->hasFlag(DF_FRIEND));
  xassert(!var->hasFlag(DF_NAMESPACE));
  xassert(var->isMember());
  return true;
}

// find the MemberInitializer that initializes data member memberVar;
// return NULL if none
MemberInit *ElabVisitor::findMemberInitDataMember
  (FakeList<MemberInit> *inits, // the inits to search
   Variable *memberVar)         // data member to search for the MemberInit for
{
  MemberInit *ret = NULL;
  FAKELIST_FOREACH_NC(MemberInit, inits, mi) {
    xassert(!mi->base || !mi->member); // MemberInit should do only one thing
    if (mi->member == memberVar) {
      xassert(!ret);            // >1 MemberInit; FIX: this is a user error, not our error
      ret = mi;
    }
  }
  return ret;
}

// find the MemberInitializer that initializes data member memberVar;
// return NULL if none
MemberInit *ElabVisitor::findMemberInitSuperclass
  (FakeList<MemberInit> *inits, // the inits to search
   CompoundType *superclass)    // superclass to search for the MemberInit for
{
  MemberInit *ret = NULL;
  FAKELIST_FOREACH_NC(MemberInit, inits, mi) {
    xassert(!mi->base || !mi->member); // MemberInit should do only one thing
    if (mi->base == superclass) {
      xassert(!ret);            // >1 MemberInit; FIX: this is a user error, not our error
      ret = mi;
    }
  }
  return ret;
}


// Finish supplying to a ctor the no-arg MemberInits for unmentioned
// superclasses and members.
void ElabVisitor::completeNoArgMemberInits(Function *ctor, CompoundType *ct)
{
  SourceLoc loc = ctor->getLoc();

  // Iterate through the members in the declaration order (what is in
  // the CompoundType).  For each one, check to see if we have a
  // MemberInit for it.  If so, append that (prepend and revese
  // later); otherwise, make one.  This has the effect of
  // canonicalizing the MemberInit call order even if none needed to
  // be added, which I think is in the spec; at least g++ does it (and
  // gives a warning, which I won't do.)
  FakeList<MemberInit> *oldInits = ctor->inits;
  // NOTE: you can't make a new list of inits that is a FakeList
  // because we are still traversing over the old one.  Linked lists
  // are a premature optimization!
  SObjList<MemberInit> newInits;
  // NOTE: don't do this!
//    FakeList<MemberInit> *newInits = FakeList<MemberInit>::emptyList();
  
  FOREACH_OBJLIST(BaseClass, ct->bases, iter) {
    BaseClass const *base = iter.data();
    // omit initialization of virtual base classes, whether direct
    // virtual or indirect virtual.  See cppstd 12.6.2 and the
    // implementation of Function::tcheck_memberInits()
    //
    // FIX: We really should be initializing the direct virtual bases,
    // but the logic is so complex I'm just going to omit it for now
    // and err on the side of not calling enough initializers;
    // UPDATE: the spec says we can do it multiple times for copy
    // assign operator, so I wonder if that holds for ctors also.
    if (!ct->hasVirtualBase(base->ct)) {
      MemberInit *mi = findMemberInitSuperclass(oldInits, base->ct);
      if (!mi) {
        PQName *name = new PQ_variable(loc, base->ct->typedefVar);
        mi = new MemberInit(name, emptyArgs());
        mi->base = base->ct;
        mi->ctorVar = getDefaultCtor(str, base->ct);
      }
      newInits.prepend(mi);
    } else {
//        cerr << "Omitting a direct base that is also a virtual base" << endl;
    }
  }
  // FIX: virtual bases omitted for now
  //
  // sm: note that this code drops (user-supplied!) initializers for
  // virtual bases on the floor

  SFOREACH_OBJLIST_NC(Variable, ct->dataMembers, iter) {
    Variable *var = iter.data();
    if (!wantsMemberInit(var)) continue;
    MemberInit *mi = findMemberInitDataMember(oldInits, var);
    // It seems that ints etc. shouldn't have explicit no-arg ctors.
    // Actually, it seems that even some classes are not default
    // initialized!  However, if they are of POD type and I default
    // initialize them anyway, all I'm doing is calling their
    // implicitly-defined no-arg ctor, which (eventually) will simply do
    // nothing for the scalar data members, which is equivalent.
    // 12.6.2 para 4: If a given nonstatic data member or base class is
    // not named by a mem-initializer-id, then
    // -- If the entity is a nonstatic data member of ... class type (or
    // array thereof) or a base class, and the entity class is a non-POD
    // class, the entity is default-initialized (8.5). ....
    // -- Otherwise, the entity is not initialized. ....
    if (!mi && var->type->isCompoundType()) {
      mi = new MemberInit(new PQ_name(loc, var->name), emptyArgs());
      mi->member = var;
      mi->ctorVar = getDefaultCtor(env.str, var->type->asCompoundType());
    }
    if (mi) newInits.prepend(mi);
  }

  // *Now* we can destroy the linked list structure and rebuild it
  // again while also reversing the list.
  ctor->inits = FakeList<MemberInit>::emptyList();
  SFOREACH_OBJLIST_NC(MemberInit, newInits, iter) {
    MemberInit *mi = iter.data();
    mi->next = NULL;
    ctor->inits = ctor->inits->prepend(mi);
  }
}


// ---------------- make compiler-supplied member funcs -------------=
// make no-arg ctor ****************

// mirrors Env::receiverParameter()
Variable *ElabVisitor::makeCtorReceiver(SourceLoc loc, CompoundType *ct)
{
  Type *recType = tfac.makeTypeOf_receiver(loc, ct, CV_NONE, NULL /*syntax*/);
  return makeVariable(loc, receiverName, recType, DF_PARAMETER);
}

// for EA_IMPLICIT_MEMBER_DEFN
MR_func *ElabVisitor::makeNoArgCtorBody(CompoundType *ct, Variable *ctor)
{
  SourceLoc loc = ctor->loc;

  // empty body
  S_compound *body = makeS_compound(loc);

  // NOTE: The MemberInitializers will be added by
  // completeNoArgMemberInits() during later elaboration, so we don't
  // add them now.
  FakeList<MemberInit> *inits = FakeList<MemberInit>::emptyList();

  Function *f = makeFunction(loc, ctor, inits, body);
  f->receiver = env.makeCtorReceiver(loc, ct);

  return new MR_func(loc, f);
}


// make copy ctor ****************

MemberInit *ElabVisitor::makeCopyCtorMemberInit(
  Variable *target,          // member or base class to initialize
  Variable *srcParam,        // "__other" parameter to the copy ctor
  SourceLoc loc)
{
  // compound, if class-valued (if not, we're initializing a member
  // that is not class-valued, so it's effectively just an assignment)
  CompoundType *targetCt = target->type->ifCompoundType();

  // expression referring to "__other"
  Expression *expr = makeE_variable(loc, srcParam);

  // are we initializing a member?  if not, it's a base class subobject
  bool isMember = !target->hasFlag(DF_TYPEDEF);
  if (isMember) {
    // expression: "__other.<member>"
    expr = makeE_fieldAcc(loc, expr, target);
  }

  //           ArgExpression:
  ArgExpression *argExpr = new ArgExpression(expr);
  //         args:
  FakeList<ArgExpression> *args = FakeList<ArgExpression>::makeList(argExpr);
  //           name = A
  //           loc = ../oink/ctor1.cc:12:7
  //         PQ_name:

  //       MemberInit:
  MemberInit *mi = new MemberInit(new PQ_variable(loc, target), args);
  push(mi->getAnnot());
  if (isMember) {
    mi->member = target;
  }
  else {
    mi->base = targetCt;
  }
  mi->ctorVar = targetCt? getCopyCtor(env.str, targetCt) : NULL;
  if (mi->ctorVar) {
    mi->ctorStatement = makeCtorStatement
      (loc,
       env.makeE_variable(loc, target),
       target->type,
       mi->ctorVar,
       mi->args);
  }
  pop(mi->getAnnot());
  return mi;
}


// for EA_IMPLICIT_MEMBER_DEFN
MR_func *ElabVisitor::makeCopyCtorBody(CompoundType *ct, Variable *ctor)
{
  // reversed print AST output; remember to read going up even for the
  // tree leaves

  SourceLoc loc = ctor->loc;

  // empty body
  S_compound *body = makeS_compound(loc);

  // the parameter that refers to the source object
  Variable *srcParam = ctor->type->asFunctionType()->params.first();
  //StringRef srcNameS = env.str.add("__other");

  // for each member, make a call to its copy ctor; Note that this
  // works for simple types also; NOTE: We build this in reverse and
  // then reverse it.
  FakeList<MemberInit> *inits = FakeList<MemberInit>::emptyList();
  {
    FOREACH_OBJLIST(BaseClass, ct->bases, iter) {
      BaseClass const *base = iter.data();
      // omit initialization of virtual base classes, whether direct
      // virtual or indirect virtual.  See cppstd 12.6.2 and the
      // implementation of Function::tcheck_memberInits()
      //
      // FIX: We really should be initializing the direct virtual bases,
      // but the logic is so complex I'm just going to omit it for now
      // and err on the side of not calling enough initializers
      if (!ct->hasVirtualBase(base->ct)) {
        MemberInit *mi =
          makeCopyCtorMemberInit(base->ct->typedefVar, srcParam, loc);
        inits = inits->prepend(mi);
      }
      else {
        //cerr << "Omitting a direct base that is also a virtual base" << endl;
      }
    }

    // FIX: What the heck do I do for virtual bases?  This surely isn't
    // right.
    //
    // Also, it seems that the order of interleaving of the virtual and
    // non-virtual bases has been lost.  Have to be careful of this when
    // we pretty print.
    //
    // FIX: This code is broken anyway.
  //    FOREACH_OBJLIST_NC(BaseClassSubobj, ct->virtualBases, iter) {
  //      BaseClass *base = iter->data();
  // // This must not mean what I think.
  // //     xassert(base->isVirtual);
  //      MemberInit *mi = makeCopyCtorMemberInit(base->ct->name, srcNameS, NULL, loc);
  //      inits = inits->prepend(mi);
  //    }

    SFOREACH_OBJLIST_NC(Variable, ct->dataMembers, iter) {
      Variable *var = iter.data();
      if (!wantsMemberInit(var)) continue;
      MemberInit *mi = makeCopyCtorMemberInit(var, srcParam, loc);
      inits = inits->prepend(mi);
    }

    //     inits:
    inits = inits->reverse();
  }

  Function *f = makeFunction(loc, ctor, inits, body);
  f->receiver = env.makeCtorReceiver(loc, ct);

  return new MR_func(loc, f);
}


// make copy assign op ****************

// "return *this;"
S_return *ElabVisitor::make_S_return_this(SourceLoc loc)
{
  // "return *this;"
  return new S_return(loc, loc, new FullExpression(makeThisRef(loc)));
}

// "this->y = __other.y;"
S_expr *ElabVisitor::make_S_expr_memberCopyAssign
  (SourceLoc loc, Variable *member, Variable *other)
{
  // "__other.y"
  E_fieldAcc *otherDotY = makeE_fieldAcc(loc, makeE_variable(loc, other), member);

  Expression *action = NULL;
  if (member->type->isCompoundType()) {
    CompoundType *ct = member->type->asCompoundType();

    // use a call to the assignment operator
    Variable *assign = getAssignOperator(env.str, ct);

    if (assign && !assign->isBuiltin) {
      // "(*this).y.operator=(__other.y)"
      action = makeMemberCall(loc,
                              makeE_fieldAcc(loc, makeThisRef(loc), member) /*y*/,
                              assign,
                              makeExprList1(otherDotY));
    }
    else {
      // bhackett: fallthrough and use E_assign. downstream we will interpret
      // this as assigning between each field of the type.
    }
  }

  if (!action) {
    // use the E_assign built-in operator

    // "(*this).y = other.y"
    action = new E_assign(makeE_fieldAcc(loc, makeThisRef(loc), member),
                          BIN_ASSIGN,
                          otherDotY);
    action->type = otherDotY->type;
  }

  // wrap up as a statement
  return makeS_expr(loc, action);
}

// "this->W::operator=(__other);"
Statement *ElabVisitor::make_statement_superclassCopyAssign
  (SourceLoc loc, CompoundType *w, Variable *other)
{
  // "W::operator="
  Variable *assign = getAssignOperator(env.str, w);
  if (assign && !assign->isBuiltin) {
    // "this->W::operator=(__other)"
    E_funCall *call = makeMemberCall(loc, makeThisRef(loc), assign,
                                   makeExprList1(makeE_variable(loc, other)));

    // "this->W::operator=(__other);"
    return makeS_expr(loc, call);
  }
  else {
    // just inline assignment of the fields for the base class.
    S_compound *s = makeS_compound(loc);
    fill_S_compound_assignBody(loc, w, other, &s->stmts);
    return s;
  }
}

void ElabVisitor::fill_S_compound_assignBody
  (SourceLoc loc, CompoundType *ct, Variable *other,
   ASTList<Statement> *stmts)
{
  // NOTE: these are made and appended *in* *order*, not in reverse
  // and then reversed as with the copy ctor

  // For each superclass, make the call to operator =.
  FOREACH_OBJLIST(BaseClass, ct->bases, iter) {
    BaseClass const *base = iter.data();
    // omit initialization of virtual base classes, whether direct
    // virtual or indirect virtual.  See cppstd 12.6.2 and the
    // implementation of Function::tcheck_memberInits()
    //
    // FIX: We really should be initializing the direct virtual bases,
    // but the logic is so complex I'm just going to omit it for now
    // and err on the side of not calling enough initializers
    if (!ct->hasVirtualBase(base->ct)) {
      stmts->append(make_statement_superclassCopyAssign(loc, base->ct, other));
    }
  }

  SFOREACH_OBJLIST_NC(Variable, ct->dataMembers, iter) {
    Variable *var = iter.data();
    if (!wantsMemberInit(var)) continue;
    // skip assigning to const or reference members; NOTE: this is an
    // asymmetry with copy ctor, which can INITIALIZE const or ref
    // types, however we cannot ASSIGN to them.
    //
    // sm: The existence of consts or refs means that the assignment
    // operator cannot be called, according to the spec.  But the
    // behavior of the code here seems fine.
    Type *type = var->type;
    if (type->isReference() || type->isConst()) continue;
    stmts->append(make_S_expr_memberCopyAssign(loc, var, other));
  }
}


//  12.8 paragraph 10
//
//  If the lass definition does not explicitly declare a copy assignment
//  operator, one is declared implicitly.  The implicitly-declared copy
//  assignment operator for a class X will have the form
//
//          X& X::operator=(X const &)
//
//  if [lots of complicated conditions here on whether or not the
//  parameter should be a reference to const or not; I'm just going to
//  make it const for now] ...
//
//  paragraph 13
//
//  The implicitly-defined copy assignment operator for class X performs
//  memberwise assignment of its subobjects.  ...
//
//  sm: I removed some large passages that are not directly relevant
//  to the operation of this function.  The standard is a copyrighted work
//  and we should therefore only include brief segments that are highly
//  relevant.
//
// for EA_IMPLICIT_MEMBER_DEFN
MR_func *ElabVisitor::makeCopyAssignBody
  (SourceLoc loc, CompoundType *ct, Variable *assign)
{
  // get the source parameter, called "__other" (0th param is receiver
  // object, so 1st is __other)
  FunctionType *assignFt = assign->type->asFunctionType();
  xassert(assignFt->params.count() == 2);

  Variable *other = assignFt->params.nth(1);

  // we make the function now, before filling in 'stmts', because
  // while we're filling in 'stmts' we want 'f' on the function stack
  Function *f = makeFunction(loc, assign,
                             FakeList<MemberInit>::emptyList(),    // inits
                             makeS_compound(loc));
  functionStack.push(f);

  // get ahold of the statement list to build
  ASTList<Statement> *stmts = &(f->body->stmts);

  // fill in assignments and calls for the base classes and data members.
  fill_S_compound_assignBody(loc, ct, other, stmts);

  stmts->append(make_S_return_this(loc));

  functionStack.pop();
  return new MR_func(loc, f);
}


// make implicit dtor ****************

// "a.~A();"
Statement *ElabVisitor::make_S_memberDtor
  (SourceLoc loc, Expression *member, CompoundType *memberType)
{
  // "~A"
  Variable *dtor = getDtor(env.str, memberType);

  if (dtor) {
    // "a.~A()"
    E_funCall *funcall = makeMemberCall(loc, member, dtor, emptyArgs());

    // "a.~A();"
    return makeS_expr(loc, funcall);
  }
  else {
    // bhackett: fix if there were parse/tcheck errors.
    return new S_skip(loc, loc);
  }
}

// for EA_MEMBER_DTOR
void ElabVisitor::completeDtorCalls(
  Function *func,      // destructor being annotated
  CompoundType *ct)    // the class of which 'func' is a member
{
  SourceLoc loc = func->getLoc();

  // We add to the statements in *forward* order, unlike when adding
  // to MemberInitializers, but since this is a dtor, not a ctor, we
  // *do* have to do it in reverse.
  SObjStack<Statement> dtorStmtsReverse;

  FOREACH_OBJLIST(BaseClass, ct->bases, iter) {
    BaseClass const *base = iter.data();
    // omit initialization of virtual base classes, whether direct
    // virtual or indirect virtual.  See cppstd 12.6.2 and the
    // implementation of Function::tcheck_memberInits()
    //
    // FIX: We really should be initializing the direct virtual bases,
    // but the logic is so complex I'm just going to omit it for now
    // and err on the side of not calling enough destructors
    if (!ct->hasVirtualBase(base->ct)) {
      dtorStmtsReverse.push(
        make_S_memberDtor(loc, makeThisRef(loc), base->ct));
    }
  }

  SFOREACH_OBJLIST_NC(Variable, ct->dataMembers, iter) {
    Variable *var = iter.data();
    if (!wantsMemberInit(var)) continue;
    if (!var->type->isCompoundType()) continue;
    dtorStmtsReverse.push(
      make_S_memberDtor(loc, makeE_variable(loc, var), 
                             var->type->asCompoundType()));
  }

  // reverse and append to the statements list
  ASTList<Statement> *dtorStatements = new ASTList<Statement>();
  while (!dtorStmtsReverse.isEmpty()) {
    dtorStatements->append(dtorStmtsReverse.pop());
  }     

  // FIX: I can't figure out the bug right now, but in/t0019.cc fails
  // with a seg fault if I put this line *before* the while loop
  // above.  From looking at the data structures, it seems that it
  // shouldn't matter.
  //
  // sm: the reason is that creating an S_compound *deletes* the
  // ASTList<Statement> that is passed to it
  func->dtorStatement = new S_compound(loc, loc, dtorStatements);
}

// for EA_IMPLICIT_MEMBER_DEFN
MR_func *ElabVisitor::makeDtorBody(CompoundType *ct, Variable *dtor)
{
  SourceLoc loc = dtor->loc;

  // function with empty body; the member dtors will be elaborated later
  Function *f = makeFunction(loc, dtor,
                             FakeList<MemberInit>::emptyList(),   // inits
                             makeS_compound(loc));

  return new MR_func(loc, f);
}


// -------------------- special function queries -----------------------
// a filter on elements of an overload set of members in 'ct'
typedef bool (*OverloadFilter)(CompoundType *ct, FunctionType *ft);

Variable *overloadSetFilter(CompoundType *ct, Variable *start, OverloadFilter func)
{
  if (!start || !start->type->isFunctionType()) {
    return NULL;               // name maps to no function
  }

  if (!start->overload) {
    if (func(ct, start->type->asFunctionType())) {
      return start;            // name maps to one thing, it passes
    }
    else {
      return NULL;             // name maps to one thing, it fails
    }
  }

  // name maps to multiple things, consider each
  SFOREACH_OBJLIST_NC(Variable, start->overload->set, iter) {
    if (func(ct, iter.data()->type->asFunctionType())) {
      return iter.data();      // the first one that passes
    }
  }

  return NULL;                 // none pass
}


static bool defaultCtorTest(CompoundType *ct, FunctionType *ft)
{
  // every parameter must have a default value
  return ft->paramsHaveDefaultsPast(0);
}

Variable* getDefaultCtor(StringTable &str, CompoundType *ct)
{
  return overloadSetFilter(ct, ct->rawLookupVariable(str("constructor-special")),
                           defaultCtorTest);
}


// true if parameter 'n' is a reference to 'ct'
static bool nthIsCtReference(CompoundType *ct, FunctionType *ft, int n,
                             bool mustBeReference = true)
{
  if (ft->params.count() <= n) {
    return false;
  }
  Type *t = ft->params.nth(n)->type;
  if ((!mustBeReference || t->isReference()) &&
      t->asRval()->ifCompoundType() == ct) {
    return true;
  }
  else {
    return false;
  }
}

static bool copyCtorTest(CompoundType *ct, FunctionType *ft)
{
  return
    nthIsCtReference(ct, ft, 0) &&   // first param must be a reference to 'ct'
    ft->paramsHaveDefaultsPast(1);   // subsequent have defaults
}

Variable* getCopyCtor(StringTable &str, CompoundType *ct)
{
  return overloadSetFilter(ct, ct->rawLookupVariable(str("constructor-special")),
                           copyCtorTest);
}


static bool assignOperatorTest(CompoundType *ct, FunctionType *ft)
{
  return
    ft->isMethod() &&                // first param is receiver object
    nthIsCtReference(ct, ft, 1,      // second param must be a reference to 'ct'
      false /*mustBeReference*/) &&  //   12.8p9 allows non-ref (in/t0560.cc)
    ft->paramsHaveDefaultsPast(2);   // subsequent have defaults
}

Variable* getAssignOperator(StringTable &str, CompoundType *ct)
{
  return overloadSetFilter(ct, ct->rawLookupVariable(str("operator=")),
                           assignOperatorTest);
}


Variable* getDtor(StringTable &str, CompoundType *ct)
{
  // synthesize the dtor name... maybe I should be using
  // "destructor-special" or something
  return ct->rawLookupVariable(str(stringc << "~" << ct->name));
}


// --------------------- exception stuff ------------------
// for EA_GLOBAL_EXCEPTION
void Handler::elaborate(ElabVisitor &env)
{
  SourceLoc loc = body->loc;

  // sm: grumble grumble, this code makes no sense... a separate
  // global for every handler?  who interacts with all these globals?
  // certainly not E_throw...

  // NOTE: don't do this if it is just a *ref* to a CompoundType.
  // Those are dtored later since the reference captures the global
  // and prevents it from being dtored now.  FIX: we have to deal with
  // this reference-capture problem just as with "A &a = A();"
  // UPDATE: Well, I at least need to make the variable if it is a
  // ref, so I'll make the dtor also.
  Type *typeIdType = typeId->getType();
  if (typeIdType->asRval()->isCompoundType()) {
    if (!globalVar) {
      globalVar = env.makeVariable(loc, env.makeCatchClauseVarName(),
                                   typeIdType->asRval(),
                                   DF_STATIC // I think it is a static global
                                   | DF_GLOBAL);

      // if we catch by value, we need a copy ctor into a temporary
      // which is passed into the handler; in other words, we treat
      // passing the global exception to the handler as if it were a
      // function call
      if (typeIdType->isCompoundType()) {
        localArg = env.elaborateCallByValue
          (loc, typeIdType,
           env.makeE_variable(loc, globalVar) // NOTE: elaborateCallByValue() won't clone this
           );
      }

      // Scott doesn't like the idea of this being here, but it has to
      // go somewhere, and, just as we don't have a "global" space in
      // which to put the globalVar, we don't have a "global" place to
      // put its dtor, so I put them together.
      globalDtorStatement =
        env.makeDtorStatement(loc,
                              // no need to clone the target as
                              // makeE_variable() makes all new AST
                              env.makeE_variable(loc, globalVar),
                              // can only make a dtor for a CompoundType, not a ref to one
                              typeIdType->asRval());
    }
  }
}


// for EA_GLOBAL_EXCEPTION
bool E_throw::elaborate(ElabVisitor &env)
{
  if (!expr) {
    return false;     // no children anyway
  }

  // sm: I think what follows is wrong:
  //   - 'globalVar' is created, but a declaration is not, so
  //     an analysis might be confused by its sudden appearance
  //   - the same object is used for all types, but makeCtorStatement
  //     is invoked with different types.. it's weird
  //   - the whole thing with throwClauseSerialNumber is bad.. it
  //     *should* be a member of Env, and set from the outside after
  //     construction if a wrapper analysis wants the numbers to not
  //     be re-used

  // sm: there is no location handy, and it wouldn't make sense anyway
  // because it makes no sense to associate a new global with every E_throw!
  // ok, maybe I'm being harsh.. but there's still no loc handy
  SourceLoc loc = SL_UNKNOWN;

  // If it is a throw by value, it gets copy ctored somewhere, which
  // in an implementation is some anonymous global.  I can't think of
  // where the heck to make these globals or how to organize them, so
  // I just make it in the throw itself.  Some analysis can come
  // through and figure out how to hook these up to their catch
  // clauses.
  Type *exprType = expr->getType()->asRval();
  if (exprType->isCompoundType()) {
    if (!globalVar) {
      globalVar = env.makeVariable(loc, env.makeThrowClauseVarName(),
                                   exprType,
                                   DF_STATIC // I think it is a static global
                                   | DF_GLOBAL);

      // clone the expr, putting the clone back into 'expr', and using
      // the original (tcheck'd) one in 'makeCtorStatement' (SCS)
      Expression *origExpr = expr;
      expr = env.cloneExpr(expr);

      globalCtorStatement =
        env.makeCtorStatement(loc, env.makeE_variable(loc, globalVar), exprType,
                              getCopyCtor(env.str, exprType->asCompoundType()),
                              makeExprList1(origExpr));
                              
      return false;     // SES
    }
  }                           
  
  return true;
}


// ------------------------ new/delete ---------------------------
bool E_new::elaborate(ElabVisitor &env)
{
  SourceLoc loc = env.enclosingStmtLoc;

  // TODO: this doesn't work for new[]

  // sm: This is way wrong.  It pretends that 'new' yields a reference
  // to the same global instance over and over.  The code should
  // instead do something like:
  //   C *temp = ::operator new(sizeof(C));
  //   temp <- C::C();      // 'temp' is 'retObj'
  //   temp                 // the value of the E_new expression

  // the type of the elements to create
  Type *t = atype->getType();

  if (t->isCompoundType()) {
    heapVar = env.makeVariable(loc, env.makeE_newVarName(), t, DF_NONE);

    FakeList<ArgExpression> *args0 = env.emptyArgs();
    if (ctorArgs) {
      // original is used in elaboration, clone stays behind (SCS)
      args0 = ctorArgs->list;
      ctorArgs->list = env.cloneExprList(ctorArgs->list);
    }

    ctorStatement = env.makeCtorStatement(loc, env.makeE_variable(loc, heapVar), t,
                                          ctorVar, args0);
    return false;    // SES
  }

  return true;
}


bool E_delete::elaborate(ElabVisitor &env)
{
  SourceLoc loc = env.enclosingStmtLoc;

  // TODO: this doesn't work for delete[]

  // the type of the argument to 'delete', typically a pointer to
  // the type of the elements to destroy
  Type *t = expr->type->asRval();

  // E_delete::itcheck_x() should have noticed that its not a pointer
  // and aborted before calling us if it wasn't.
  if (!t->isPointerType())
    return true;

  PointerType *to = t->asPointerType();
  if (to->atType->isCompoundType()) {
    if (!to->atType->asCompoundType()->isComplete()) {
      // 10/03/04: cppstd 5.3.5 para 5 explains that, while it *is*
      // legal to delete an incomplete type, the destructor (once the
      // type is completed) must be trivial (otherwise the program has
      // undefined behavior); so Elsa will assume that the dtor is in
      // fact trivial
      return true;
    }

    // use orig in elaboration, clone stays behind.
    // make sure we don't delete the clone, as it is still needed
    // to do the actual free() after the dtor finishes.
    Expression *origExpr = expr;
    expr = expr->clone();

    E_deref *deref = new E_deref(origExpr);
    deref->type = env.tfac.makeReferenceType(to->atType);

    dtorStatement = env.makeDtorStatement
      (loc,
       deref,
       to->atType               // no need to clone this type; it is not stored
       );
       
    return false;     // SES
  }

  return true;
}


// ----------------------- S_return -----------------------
// for EA_ELIM_RETURN_BY_VALUE
bool S_return::elaborate(ElabVisitor &env)
{
  if (expr) {
    FunctionType *ft = env.functionStack.top()->funcType;
    xassert(ft);

    // FIX: check that ft->retType is non-NULL; I'll put an assert for now
    // sm: FunctionType::retType is never NULL ...
    xassert(ft->retType);

    if (ft->retType->isCompoundType()) {
      CompoundType *retTypeCt = ft->retType->asCompoundType();

      // This is an instance of return by value of a compound type.
      // We accomplish this by calling the copy ctor.

      // get the target of the constructor function
      E_variable *retVar = env.makeE_variable(loc, env.functionStack.top()->retVar);

      // since the S_return itself will be visited before the subexpr,
      // we know the expr here has not yet been elaborated, so will not
      // yet have put any temporaries into the fullexp
      xassert(expr->getAnnot()->noTemporaries());

      // get the arguments of the constructor function; NOTE: we dig
      // down below the FullExpression to the raw Expression
      Expression *subExpr = expr->expr;
      FakeList<ArgExpression> *args0 =
        FakeList<ArgExpression>::makeList(new ArgExpression(subExpr));
      xassert(args0->count() == 1);      // makeList always returns a singleton list

      // make the constructor function
      env.push(expr->getAnnot());// e.g. in/d0049.cc breaks w/o this
      ctorStatement = env.makeCtorStatement(loc, retVar, ft->retType,
                                            getCopyCtor(env.str, retTypeCt), args0);
      env.pop(expr->getAnnot());

      // make the original expression a clone
      expr->expr = env.cloneExpr(expr->expr);

      //xassert(expr->expr);

      // traverse only the elaboration
      //ctorStatement->traverse(env);    // 'makeCtorStatement' does this internally
      return false;
    }
  }

  return true;     // traverse 'expr'
}


// ===================== ElabVisitor =========================
// ----------------------- TopForm ---------------------------
bool ElabVisitor::visitTopForm(TopForm *tf)
{
  static int elabTopForm = 0;
  ++elabTopForm;
  TRACE("elabtopform", elabTopForm);
  if (doing(EA_VARIABLE_DECL_CDTOR) &&
      tf->isTF_decl()) {
    // global variables
    elaborateCDtorsDeclaration(tf->asTF_decl()->decl);
    return false;     // SES (e.g. in/d0027.cc breaks if we return true)
  } 
  
  return true;
}


// ----------------------- Function ---------------------------
bool ElabVisitor::visitFunction(Function *f)
{
  // don't elaborate function bodies that were never typechecked
  if (f->instButNotTchecked()) {
    return false;               // prune
  }

  functionStack.push(f);
  FunctionType *ft = f->funcType;

  if (doing(EA_ELIM_RETURN_BY_VALUE)) {
    elaborateFunctionStart(f);
  }

  if (doing(EA_MEMBER_DTOR) &&
      ft->isDestructor()) {

    // bhackett: sometimes the destructor is not a member
    // with parse/tcheck errors. huh.
    if (ft->isMethod())
      completeDtorCalls(f, ft->getClassOfMember());
  }

  if (doing(EA_IMPLICIT_MEMBER_CTORS) &&
      ft->isConstructor()) {
    // pull out the compound that this ctor creates
    CompoundType *ct = f->receiver->type->asReferenceType()->
                          atType->asCompoundType();
    completeNoArgMemberInits(f, ct);
  } 
  
  return true;
}


void ElabVisitor::postvisitFunction(Function *)
{
  functionStack.pop();
}


// ---------------------- MemberInit ---------------------------
bool ElabVisitor::visitMemberInit(MemberInit *mi)
{
  push(mi->getAnnot());

  Function *func = functionStack.top();
  SourceLoc loc = mi->name->loc;

  // should already be tchecked, and either be a member or base class subobject
  // bhackett: disable. can crop up if there were tcheck errors.
  // xassert(mi->member || mi->base);

  // TODO: use assignments instead of ctors for non-class-valued objects

  if (doing(EA_MEMBER_CTOR) &&
      mi->ctorVar) {
    // clone the arguments, but use the original tcheck'd version as
    // what will subsequently be elaborated
    FakeList<ArgExpression> *orig = mi->args;
    FakeList<ArgExpression> *cloned = env.cloneExprList(mi->args);
    mi->args = cloned;

    if (mi->member) {
      // initializing a data member
      mi->ctorStatement = makeCtorStatement
        (loc, makeE_variable(loc, mi->member), mi->member->type,
         mi->ctorVar, orig);
    }

    else {
      // initializing a base class subobject

      // need a Type for the eventual E_constructor...
      Type *type = tfac.makeCVAtomicType(mi->base, CV_NONE);

      mi->ctorStatement = makeCtorStatement
        (loc, makeE_variable(loc, func->receiver), type,
         mi->ctorVar, orig);
    }

    // elaborate the ctorStatement only (not the 'args')
    //mi->ctorStatement->traverse(this->loweredVisitor); // 'makeCtorStatement' does this internally

    pop(mi->getAnnot());// b/c when I return false, postvisit isn't called
    return false;       // don't automatically traverse children, esp. 'args' (SES)
  }

  else {
    return true;        // automatically traverse, elaborate 'args'
  }
}

void ElabVisitor::postvisitMemberInit(MemberInit *mi)
{
  pop(mi->getAnnot());
}


// -------------------- TypeSpecifier --------------------------
bool ElabVisitor::visitTypeSpecifier(TypeSpecifier *ts)
{
  if (doing(EA_IMPLICIT_MEMBER_DEFN) &&
      ts->isTS_classSpec()) {
    TS_classSpec *spec = ts->asTS_classSpec();
    SourceLoc loc = spec->loc;
    CompoundType *ct = spec->ctype;

    if (!ct->name) {
      return true;      // bail on anonymous classes, since 'addCompilerSuppliedDecls' does
    }

    // default ctor
    {
      // is there an implicit decl?
      Variable *var = getDefaultCtor(env.str, ct);
      if (var && var->isImplicitMemberFunc()) {
        spec->members->list.append(makeNoArgCtorBody(ct, var));
      }
    }

    // copy ctor
    {
      // is there an implicit decl?
      Variable *var = getCopyCtor(env.str, ct);
      if (var && var->isImplicitMemberFunc()) {
        spec->members->list.append(makeCopyCtorBody(ct, var));
      }
    }

    // assignment operator
    {
      // is there an implicit decl?
      Variable *var = getAssignOperator(env.str, ct);
      if (var && var->isImplicitMemberFunc()) {
        spec->members->list.append(makeCopyAssignBody(loc, ct, var));
      }
    }

    // dtor
    {
      // is there an implicit decl?
      Variable *var = getDtor(env.str, ct);
      if (var && var->isImplicitMemberFunc()) {
        spec->members->list.append(makeDtorBody(ct, var));
      }
    }

    // NOTE: In the code above, we have added to 'members->list', which
    // means that the added elements *will* be traversed after this
    // function returns, as part of the usual subtree traversal.
  }

  return true;     // traverse children (subtrees)
}


// ------------------------ Member -----------------------------
bool ElabVisitor::visitMember(Member *m)
{           
  // Calling 'elaborateCDtorsDeclaration' wouldn't make sense because
  // ctors need to depend on member init arguments, and dtors are more
  // easily handled by adding them to the containing dtors.
  #if 0
  if (doing(EA_MEMBER_DECL_CDTOR) &&
      m->isMR_decl()) {
    // members
    elaborateCDtorsDeclaration(m->asMR_decl()->d);
    return false;    // SES
  }
  #endif // 0

  return true;
}


// ----------------------- Statement ---------------------------
bool ElabVisitor::visitStatement(Statement *s)
{
  enclosingStmtLoc = s->loc;

  if (doing(EA_ELIM_RETURN_BY_VALUE) &&
      s->isS_return()) {
    return s->asS_return()->elaborate(*this);
  }

  if (doing(EA_VARIABLE_DECL_CDTOR) &&
      s->isS_decl()) {
    // local variables
    elaborateCDtorsDeclaration(s->asS_decl()->decl);
    return false;      // SES
  }

  return true;
}


// --------------------- Condition ------------------------
bool ElabVisitor::visitCondition(Condition *c)
{
  if (doing(EA_VARIABLE_DECL_CDTOR) &&
      c->isCN_decl()) {
    c->asCN_decl()->typeId->decl->elaborateCDtors(*this);
    return false;      // SES
  }                          
  
  return true;
}


// ---------------------- Handler -------------------------
bool ElabVisitor::visitHandler(Handler *h)
{
  push(h->getAnnot());

  if (doing(EA_GLOBAL_EXCEPTION)) {
    h->elaborate(*this);

    // the elaboration performed by 'h' doesn't do anything with
    // the handler body, and default elaboration won't mess with
    // the handler parameter, so it should be safe to simply allow
    // default elaboration to take care of subtrees
    return true;
  }

  return true;
}

void ElabVisitor::postvisitHandler(Handler *h)
{  
  pop(h->getAnnot());
}


// ---------------------- Expression ------------------------
bool ElabVisitor::visitExpression(Expression *e)
{
  // will have to suffice..
  SourceLoc loc = enclosingStmtLoc;

  // bhackett: sometimes tcheck doesn't assign types to expressions.
  // fix up these problems here.
  if (!e->type)
    e->type = tfac.getSimpleType(ST_ERROR);

  if (e->isE_stringLit()) {
    // There is nothing to elaborate, and I don't want to look at
    // the 'continuation' since its 'type' field is NULL.  Also,
    // this avoids dying on the NULL 'type' field of the string
    // literals in 'asm's.
    return false;
  }

  // don't elaborate template-dependent expressions
  //
  // note that if someone creates an Expression and forgets to set
  // the 'type' field, it will segfault here, so this test also
  // serves as something of an AST validator
  if (e->type->isDependent()) {
    // FIX: dsw: shouldn't this be an assertion failure now that we
    // never elaborate template definitions?
    return false;   // ignore children
  }

  if (doing(EA_GLOBAL_EXCEPTION) &&
      e->isE_throw()) {
    return e->asE_throw()->elaborate(*this);
  }

  // EA_ELIM_RETURN_BY_VALUE and EA_ELIM_PASS_BY_VALUE; the
  // individual feature tests are inside 'elaborateCallSite'
  //
  // Note that 'elaborateCallSite' produces tcheck'd AST but
  // does not finish off all elaboration, so afterwards we
  // let the visitor automatically elaborate subtrees.
  if (e->isE_funCall()) {
    E_funCall *call = e->asE_funCall();
    if (call->func->type->isFunctionType()) {
      call->retObj = elaborateCallSite(loc, call->func->type->asFunctionType(),
                                       call->args, false /*artificialCtor*/);
    }
    else {
      // things that end up here:
      //   - call sites in template functions (e.g. in/t0047.cc);
      //     maybe don't elaborate template functions at all?
      //   - calls to function objects (operator()), because our
      //     operator overload resolution doesn't fix the AST in
      //     that case
      // just let these slide for now...
    }
  }
  if (e->isE_constructor()) {
    E_constructor *call = e->asE_constructor();

    // sm: I'm replicating the logic that was originally in
    // E_constructor::inner2_itcheck, even though it's clear
    // that 'artificialCtor' is always false
    if (call->ctorVar && !call->artificial) {
      call->retObj = elaborateCallSite(loc, call->ctorVar->type->asFunctionType(),
                                       call->args, call->artificial /*artificialCtor*/);
    }
  }

  if (doing(EA_TRANSLATE_NEW) &&
      e->isE_new()) {
    return e->asE_new()->elaborate(*this);
  }
  if (doing(EA_TRANSLATE_DELETE) &&
      e->isE_delete()) {
    return e->asE_delete()->elaborate(*this);
  }

  return true;
}


// ----------------------- FullExpression ----------------------
bool ElabVisitor::visitFullExpression(FullExpression *fe)
{
  push(fe->getAnnot());
  return true;
}

void ElabVisitor::postvisitFullExpression(FullExpression *fe)
{
  pop(fe->getAnnot());
}


// ----------------------- getAnnot() ----------------------

// I construct this lazily because you can't initialize with one
// because you can't call new on a class that has only been forward
// declared.
bool MemberInit::hasAnnot() {
  return annot;
}

bool Handler::hasAnnot() {
  return annot;
}

bool FullExpression::hasAnnot() {
  return annot;
}

bool Initializer::hasAnnot() {
  return annot;
}

FullExpressionAnnot *MemberInit::getAnnot() {
  if (!annot) annot = new FullExpressionAnnot(new ASTList<Declaration>());
  return annot;
}

FullExpressionAnnot *Handler::getAnnot() {
  if (!annot) annot = new FullExpressionAnnot(new ASTList<Declaration>());
  return annot;
}

FullExpressionAnnot *FullExpression::getAnnot() {
  if (!annot) annot = new FullExpressionAnnot(new ASTList<Declaration>());
  return annot;
}

FullExpressionAnnot *Initializer::getAnnot() {
  if (!annot) annot = new FullExpressionAnnot(new ASTList<Declaration>());
  return annot;
}


// ----------------------- Initializer ----------------------
bool ElabVisitor::visitInitializer(Initializer *in)
{
  // the fullexp annots kick in only for IN_expr and IN_ctor;
  // its presence in IN_compound is a false orthogonality
  if (in->isIN_expr() || in->isIN_ctor()) {
    push(in->getAnnot());
  }

  return true;
}

void ElabVisitor::postvisitInitializer(Initializer *in)
{
  if (in->isIN_expr() || in->isIN_ctor()) {
    pop(in->getAnnot());
  }
}


// =================== extra AST nodes =====================
// ------------------------ TS_type ------------------------
Type *TS_type::itcheck(Env &env, DeclFlags dflags)
{
  return type;
}

void TS_type::print(PrintEnv &env)
{
  xfailure("I think this is not called because TS_simple::print isn't either");
}


// --------------------- PQ_variable ------------------------
StringRef PQ_variable::getName() const
{
  return var->name;
}

string PQ_variable::toComponentString() const
{
  return var->name;
}

void PQ_variable::tcheck_pq(Env &env, Scope*, LookupFlags)
{
  // nothing to check
}

void PQ_variable::print(PrintEnv &env)
{
  // this is unlikely to tcheck correctly, but that's true of
  // lots of cc_print functions..
  *env.out << var->name;
}

// EOF
