// cc_tcheck.cc            see license.txt for copyright and terms of use
// C++ typechecker, implemented as methods declared in cc_tcheck.ast

// Throughout, references are made to the ISO C++ Standard:
//
// International Organization for Standardization.
// ISO/IEC 14882:1998: Programming languages -- C++.
// International Organization for Standardization, Geneva,
// Switzerland, September 1998.
//
// These references are all marked with the string "cppstd".

#include "cc_ast.h"         // C++ AST
#include "cc_ast_aux.h"     // class LoweredASTVisitor
#include "cc_env.h"         // Env
#include "trace.h"          // trace
#include "cc_print.h"       // PrintEnv
#include "strutil.h"        // decodeEscapes
#include "cc_lang.h"        // CCLang
#include "stdconv.h"        // test_getStandardConversion
#include "implconv.h"       // test_getImplicitConversion
#include "overload.h"       // resolveOverload
#include "generic_amb.h"    // resolveAmbiguity, etc.
#include "implint.h"        // resolveImplIntAmbig
#include "ast_build.h"      // makeExprList1, etc.
#include "strutil.h"        // prefixEquals, pluraln
#include "macros.h"         // Restorer
#include "typelistiter.h"   // TypeListIter_FakeList
#include "owner.h"          // Owner
#include "mtype.h"          // MType

#include <stdlib.h>         // strtoul, strtod
#include <ctype.h>          // isdigit
#include <limits.h>         // INT_MAX, UINT_MAX, LONG_MAX

// D(): debug code
#ifdef NDEBUG
  #define D(stuff)
#else
  #define D(stuff) stuff
#endif

// forwards in this file
void tcheckPQName(PQName *&name, Env &env, Scope *scope = NULL, 
                  LookupFlags lflags = LF_NONE);

static Variable *outerResolveOverload_ctor
  (Env &env, SourceLoc loc, Type *type, ArgumentInfoArray &argInfo);

static Variable *outerResolveOverload_explicitSet(
  Env &env,
  PQName * /*nullable*/ finalName,
  SourceLoc loc,
  StringRef varName,
  ArgumentInfoArray &argInfo,
  SObjList<Variable> &candidates);

FakeList<ArgExpression> *tcheckArgExprList(FakeList<ArgExpression> *list, Env &env,
                                           ArgumentInfoArray &argInfo,
                                           Type *receiverType = NULL);

Type *resolveOverloadedUnaryOperator(
  Env &env,
  Expression *&replacement,
  Expression *ths,
  Expression *expr,
  OverloadableOp op);

void compareCtorArgsToParams(Env &env, Variable *ctor,
                             FakeList<ArgExpression> *args,
                             ArgumentInfoArray &argInfo);

bool findAnonymousField(Env &env, CompoundType *ct,
                        PQName *fieldName,
                        ArrayStack<Variable*> &anon_fields);

// return true if the list contains no disambiguating errors
bool noDisambErrors(ErrorList const &list)
{
  return !list.hasDisambErrors();
}


// 'ambiguousNodeName' is a template function in generic_amb.h, but
// declarators are special, since there's only one node type; the
// difference lies in the values of the fields (ah, the beauty of C++
// template specialization..)
string ambiguousNodeName(Declarator const *n)
{
  if (n->init) {
    return string("Declarator with initializer");
  }
  else {
    return string("Declarator without initializer");
  }
}

string ambiguousNodeName(Expression const *e)
{
  if (e->isE_new()) {
    E_new const *en = e->asE_newC();

    // the ambiguity has to do with presence of placement args
    // and/or ctor args, so report that info
    stringBuilder sb;
    sb << "E_new";
    if (en->placementArgs && en->ctorArgs) {
      sb << " with placement args and ctor args";
    }
    else if (en->placementArgs) {
      sb << " with placement args";
    }
    else if (en->ctorArgs) {
      sb << " with ctor args";
    }
    return sb;
  }
  else {
    return e->kindName();
  }
}


// little experiment: since I've implemented the "confused by earlier
// errors" mechanism, there is now a big difference between a segfault
// and an xfailure (the latter being mapped to "confused" sometimes);
// so I will try sprinkling this as a way of preventing the segfault
template <class T>
inline T *mustBeNonNull(T *ptr)
{
  xassert(ptr);
  return ptr;
}


// ------------------- UninstTemplateErrorFilter ------------------
// filter that keeps only strong messages
bool strongMsgFilter(ErrorMsg *msg)
{
  if (msg->flags & EF_STRONG) {
    // keep it
    return true;
  }
  else {
    // drop it
    TRACE("error", "dropping error arising from uninst template: " << msg->msg);
    return false;
  }
}


// take the errors, and later put them back after filtering
class UninstTemplateErrorFilter {
  Env &env;                  // environment
  ErrorList existingErrors;  // saved messages

public:
  UninstTemplateErrorFilter(Env &e)
    : env(e), existingErrors()
  {
    if (env.inUninstTemplate()) {
      existingErrors.takeMessages(env.errors);
    }
  }

  ~UninstTemplateErrorFilter()
  {
    if (env.inUninstTemplate()) {
      if (!env.doReportTemplateErrors) {
        // remove all messages that are not 'strong'
        // (see doc/permissive.txt)
        env.errors.filter(strongMsgFilter);
      }

      // now put back the saved messages
      env.errors.prependMessages(existingErrors);
    }
  }
};


// ------------------- TranslationUnit --------------------
void TranslationUnit::tcheck(Env &env)
{
  static int topForm = 0;
  FOREACH_ASTLIST_NC(TopForm, topForms, iter) {
    ++topForm;
    TRACE("topform", "--------- topform " << topForm <<
                     ", at " << toString(iter.data()->loc) <<
                     " --------");
    iter.setDataLink( iter.data()->tcheck(env) );
  }
}


// --------------------- TopForm ---------------------
TopForm *TopForm::tcheck(Env &env)
{
  if (!ambiguity) {
    itcheck(env);
    return this;
  }

  TopForm *ret = resolveImplIntAmbig(env, this);
  xassert(ret);
  return ret->tcheck(env);
}

void TF_error::itcheck(Env &env)
{}

void TF_decl::itcheck(Env &env)
{
  env.setLoc(loc);
  decl->tcheck(env, DC_TF_DECL);
}

void TF_func::itcheck(Env &env)
{
  env.setLoc(loc);
  f->tcheck(env);
}

void TF_template::itcheck(Env &env)
{
  env.setLoc(loc);
  td->tcheck(env);
}

void TF_explicitInst::itcheck(Env &env)
{
  env.setLoc(loc);

  // Q: Why even bother to implement "extern template"?  Why not just
  // treat it the same as "template"?  After all, Elsa does not
  // generate code anyway.
  //
  // A: It causes problems for input minimization.  If we instantiate
  // in response to "extern template", then when we go to minimize an
  // input w.r.t. some failure, Elsa is doing a lot more work than gcc
  // is, so usually Delta just creates some invalid code that gcc
  // accepts simply because it is not instantiating a bunch of stuff.
  //
  // Therefore, Elsa tries to do the same amount of work as gcc, and
  // that means implementing "extern template".  This does have the
  // effect of potentially masking some problems, but it is worth it.
  // And, you can unmask them by deleting "extern", at which point gcc
  // will have to instantiate too, so the playing field remains level.

  // little trick: pass the 'instFlags' down into Declarator::mid_tcheck
  d->dflags |= instFlags;

  d->tcheck(env, DC_TF_EXPLICITINST);
  
  // class instantiation?
  if (d->decllist->isEmpty()) {
    if (d->spec->isTS_elaborated()) {
      NamedAtomicType *nat = d->spec->asTS_elaborated()->atype;
      if (!nat) return;    // error recovery

      if (nat->isCompoundType() &&
          nat->asCompoundType()->isInstantiation()) {
        env.explicitlyInstantiate(nat->asCompoundType()->typedefVar, instFlags);
      }
      else {
        // catch "template class C;"
        env.error("explicit instantiation (without declarator) is only for class instantiations");
      }
    }
    else {
      // catch "template C<int>;"
      env.error("explicit instantiation (without declarator) requires \"class ...\"");
    }
  }

  // function instantiation?
  else if (d->decllist->count() == 1) {
    // instantiation is handled by declarator::mid_tcheck
  }
  
  else {
    // other template declarations are limited to one declarator, so I
    // am simply assuming the same is true of explicit instantiations,
    // even though 14.7.2 doesn't say so explicitly...
    env.error("too many declarators in explicit instantiation");
  }
}

void applyExternC(TopForm *form, DeclFlags flags)
{
  ASTSWITCH(TopForm, form) {
    ASTCASE(TF_decl, d)   d->decl->dflags |= flags;
    ASTNEXT(TF_func, f)   f->f->dflags |= flags;
    // just ignore other forms
    ASTENDCASED
  }
}

void TF_linkage::itcheck(Env &env)
{
  env.setLoc(loc);

  // dig down and apply DF_EXTERN_C to each form; this is preferable
  // to a flag in Env because this way I can be sure that DF_EXTERN_C
  // will only be applied to toplevel symbols
  if (linkageType == env.quote_C_quote) {
    FOREACH_ASTLIST_NC(TopForm, forms->topForms, iter) {
      applyExternC(iter.data(), DF_EXTERN_C);
    }
  }

  forms->tcheck(env);
}

void TF_one_linkage::itcheck(Env &env)
{
  env.setLoc(loc);

  // we need to dig down into the form to apply 'extern'
  // [cppstd 7.5 para 7]
  DeclFlags toApply = DF_EXTERN;
  if (linkageType == env.quote_C_quote) {
    toApply |= DF_EXTERN_C;
  }
  applyExternC(form, toApply);

  // typecheck the underlying form
  form->tcheck(env);
}

string collectContinuations(E_stringLit *strLit)
{
  stringBuilder sb;
  
  while (strLit) {
    sb << parseQuotedString(strLit->text);
    strLit = strLit->continuation;
  }
  
  return sb;
}

void TF_asm::itcheck(Env &env)
{
  env.setLoc(loc);

  Expression *rep = text;
  text->tcheck(env, rep);

  StringRef t = text->text;
  if (prefixEquals(t, "\"collectLookupResults")) {
    // this activates an internal diagnostic that will collect
    // the E_variable lookup results as warnings, then at the
    // end of the program, compare them to this string
    env.collectLookupResults = collectContinuations(text);
  }
}


void TF_namespaceDefn::itcheck(Env &env)
{
  env.setLoc(loc);

  // currently, what does the name refer to in this scope?
  Variable *existing = NULL;
  if (name) {
    existing = env.lookupVariable(name, LF_INNER_ONLY);
  }
  
  // violation of 7.3.1 para 2?
  if (existing && !existing->hasFlag(DF_NAMESPACE)) {
    env.error(loc, stringc
      << "attempt to redefine `" << name << "' as a namespace");

    // recovery: pretend it didn't have a name
    existing = NULL;
    name = NULL;                // dsw: this causes problems when you add it to the scope
  }
    
  Scope *s;
  if (existing) {
    // extend existing scope
    s = existing->scope;
  }
  else {
    // make new namespace
    s = env.createNamespace(loc, name);
  }

  // check the namespace body in its scope
  env.extendScope(s);
  FOREACH_ASTLIST_NC(TopForm, forms, iter) {
    iter.setDataLink( iter.data()->tcheck(env) );
  }
  env.retractScope(s);
}


void TF_namespaceDecl::itcheck(Env &env)
{
  env.setLoc(loc);
  decl->tcheck(env);
}


// --------------------- Function -----------------
void Function::tcheck(Env &env, Variable *instV)
{
  bool checkBody = env.checkFunctionBodies;

  if (env.secondPassTcheck) {
    // for the second pass, just force the use of the
    // variable computed in the first pass
    xassert(!instV);
    xassert(nameAndParams->var);
    instV = nameAndParams->var;

    if (checkBody) {
      instV->setFlag(DF_DEFINITION);
    }
  }

  // are we in a template function?
  bool inTemplate = env.scope()->hasTemplateParams();

  // only disambiguate, if template
  DisambiguateOnlyTemp disOnly(env, inTemplate /*disOnly*/);
  UninstTemplateErrorFilter errorFilter(env);

  // get return type
  Type *retTypeSpec = retspec->tcheck(env, dflags);

  // supply DF_DEFINITION?
  DeclFlags dfDefn = (checkBody? DF_DEFINITION : DF_NONE);
  if (env.lang.treatExternInlineAsPrototype &&
      dflags >= (DF_EXTERN | DF_INLINE)) {
    // gcc treats extern-inline function definitions specially:
    //
    //   http://gcc.gnu.org/onlinedocs/gcc-3.4.1/gcc/Inline.html
    //
    // I will essentially ignore them (just treat them like a
    // prototype), thus modeling the dynamic semantics of gcc when
    // optimization is turned off.  My nominal stance is that any
    // program that has an extern-inline definition that is different
    // from the ordinary (external) definition has undefined behavior.
    // A possible future extension is to check that such definitions
    // agree.
    //
    // Ah, but I can't just say 'checkBody = false' here because if
    // there are ambiguities in the body then lots of things don't
    // like it.  And anyway, tchecking the body is a good idea.  So I
    // do something a little more subtle, I claim this isn't a
    // "definition".
    dfDefn = DF_NONE;
  }

  // construct the full type of the function; this will set
  // nameAndParams->var, which includes a type, but that type might
  // use different parameter names if there is already a prototype;
  // dt.type will come back with a function type which always has the
  // parameter names for this definition
  Declarator::Tcheck dt(retTypeSpec,
                        dflags | dfDefn,
                        DC_FUNCTION);
  dt.existingVar = instV;
  nameAndParams = nameAndParams->tcheck(env, dt);
  xassert(nameAndParams->var);

  // the FunctionDefinition production in cc.gr rejects any parse
  // that does not have a D_func as the innermost declarator
  xassert(dt.type->isFunctionType());

  // grab the definition type for later use
  funcType = dt.type->asFunctionType();

  if (checkBody) {      // so this is a definition and not just a declaration
    // force the parameter and return types to be complete (8.3.5 para 6)
    env.ensureCompleteType("use as return type", funcType->retType);
    SFOREACH_OBJLIST(Variable, funcType->params, iter) {
      env.ensureCompleteType("use as parameter type", iter.data()->type);
    }
  }

  // record the definition scope for this template, since this
  // information is needed to instantiate it
  if (nameAndParams->var->templateInfo()) {
    Scope *s = env.nonTemplateScope();
    nameAndParams->var->templateInfo()->defnScope = s;

    // for this to fail, the template would have to be at block
    // scope, but that is not allowed by the grammar
    xassert(s->isPermanentScope());
  }

  if (checkBody) {
    tcheckBody(env);
  }
}

void Function::tcheckBody(Env &env)
{
  // if this is an instantiation, finish cloning before
  // trying to tcheck
  finishClone();

  // once we get into the body of a function, if we end up triggering
  // additional instantiations, they should *not* see any prevailing
  // second-pass mode
  Restorer<bool> re(env.secondPassTcheck, false);

  // location for random purposes..
  SourceLoc loc = nameAndParams->var->loc;

  // if this function was originally declared in another scope
  // (main example: it's a class member function), then start
  // by extending that scope so the function body can access
  // the class's members
  ScopeSeq qualifierScopes;
  CompoundType *inClass = NULL;
  {
    Scope *s = nameAndParams->var->scope;
    if (s) {
      inClass = s->curCompound;   // might be NULL, that's ok

      // current scope must enclose 's':
      //   - if 's' is a namespace, 7.3.1.2 para 2 says so
      //   - if 's' is a class, 9.3 para 2 says so
      // example of violation: in/std/7.3.1.2b.cc, error 2
      bool encloses = env.currentScopeAboveTemplEncloses(s);
      if (!encloses) {
        if (dflags & DF_FRIEND) {
          // (t0291.cc) a friend definition is a little funky, and (IMO)
          // 11.4 isn't terribly clear on this point, so I'll just try
          // suppressing the error in this case
        }
        else {
          env.diagnose3(env.lang.allowDefinitionsInWrongScopes, env.loc(), stringc
            << "function definition of `" << *(nameAndParams->getDeclaratorId())
            << "' must appear in a namespace that encloses the original declaration"
            << " (gcc bug allows it)");
        }
      }

      // these two lines are the key to this whole block..  I'm
      // keeping the surrounding stuff, though, because it has that
      // error report above, and simply to avoid disturbing existing
      // (working) mechanism
      env.getParentScopes(qualifierScopes, s);
      env.extendScopeSeq(qualifierScopes);

      // the innermost scope listed in 'qualifierScopes'
      // should be the same one in which the variable was
      // declared (could this be triggered by user code?)
      if (encloses && qualifierScopes.isNotEmpty()) {
        // sm: 8/11/04: At one point this assertion was weakened to a
        // condition involving matching types.  That was wrong; the
        // innermost scope must be *exactly* the declaration scope of
        // the function, otherwise we'll be looking in the wrong scope
        // for members, etc.
        xassert(s == qualifierScopes.top());
      }
    }
  }

  // the parameters will have been entered into the parameter
  // scope, but that's gone now; make a new scope for the
  // function body and enter the parameters into that
  Scope *bodyScope = env.enterScope(SK_PARAMETER, "function parameter bindings");
  bodyScope->curFunction = this;
  SFOREACH_OBJLIST_NC(Variable, funcType->params, iter) {
    Variable *v = iter.data();
    if (v->name) {
      env.addVariable(v);
    }
  }

  // is this a nonstatic member function?
  if (funcType->isMethod()) {
    this->receiver = funcType->getReceiver();

    // this would be redundant--the parameter list already got
    // added to the environment, and it included '__receiver'
    //env.addVariable(receiver);
  }

  // while ctors do not appear to the caller to accept a receiver,
  // to the ctor itself there *is* a receiver; so synthesize one
  if (nameAndParams->var->name == env.constructorSpecialName) {
    xassert(inClass);

    xassert(!receiver);
    receiver = env.receiverParameter(loc, inClass, CV_NONE,
                                     NULL /*syntax*/);

    xassert(receiver->type->isReference());   // paranoia
    env.addVariable(receiver);
  }

  // have to check the member inits after adding the parameters
  // to the environment, because the initializing expressions
  // can refer to the parameters
  tcheck_memberInits(env);


  // declare the __func__ variable
  if (env.lang.implicitFuncVariable ||
      env.lang.gccFuncBehavior == CCLang::GFB_variable) {
    // static char const __func__[] = "function-name";
    SourceLoc loc = body->loc;
    Type *charConst = env.getSimpleType(ST_CHAR, CV_CONST);
    Type *charConstArr = env.makeArrayType(charConst);

    if (env.lang.implicitFuncVariable) {
      Variable *funcVar = env.makeVariable(loc, env.string__func__,
                                           charConstArr, DF_STATIC);

      // I'm not going to add the initializer, because I'd need to make
      // an Expression AST node (which is no problem) but I don't have
      // anything to hang it off of, so it would leak.. I could add
      // a field to Function, but then I'd pay for that even when
      // 'implicitFuncVariable' is false..
      env.addVariable(funcVar);
    }

    // dsw: these two are also gcc; see
    // http://gcc.gnu.org/onlinedocs/gcc-3.4.1/gcc/Function-Names.html#Function%20Names
    if (env.lang.gccFuncBehavior == CCLang::GFB_variable) {
      env.addVariable(env.makeVariable(loc, env.string__FUNCTION__,
                                       charConstArr, DF_STATIC));
      env.addVariable(env.makeVariable(loc, env.string__PRETTY_FUNCTION__,
                                       charConstArr, DF_STATIC));
    }
  }

  // check the body in the new scope as well
  Statement *sel = body->tcheck(env);
  xassert(sel == body);     // compounds are never ambiguous

  if (handlers) {
    tcheck_handlers(env);
    
    // TODO: same checks for handlers that S_try::itcheck mentions in
    // its TODO ...
  }

  // close the new scope
  env.exitScope(bodyScope);

  // stop extending the named scope, if there was one
  env.retractScopeSeq(qualifierScopes);

  if (env.lang.treatExternInlineAsPrototype &&
      dflags >= (DF_EXTERN | DF_INLINE)) {
    // more extern-inline nonsense; skip 'funcDefn' setting
    return;
  }

  // this is a function definition; add a pointer from the
  // associated Variable
  //
  // dsw: WARNING: Due to the way function templates are instantiated it is
  // important to NOT move this line ABOVE this other line which is
  // above.
  //    if (!checkBody) {
  //      return;
  //    }
  // That is, it is important for the var of a function Declarator to
  // not have a funcDefn until after its whole body has been
  // typechecked.  See comment after 'if (!baseSyntax)' in
  // Env::instantiateTemplate()
  //
  // UPDATE: I've changed this invariant, as I need to point the
  // funcDefn at the definition even if the body has not been tchecked.

  if (nameAndParams->var->funcDefn) {
    if (nameAndParams->var->funcDefn != this)
      env.error(stringc << "multiple definitions assigned to same function symbol");
  }

  nameAndParams->var->funcDefn = this;
}


CompoundType *Function::verifyIsCtor(Env &env, char const *context)
{
  // make sure this function is a class member
  CompoundType *enclosing = NULL;
  if (nameAndParams->var->scope) {
    enclosing = nameAndParams->var->scope->curCompound;
  }
  if (!enclosing) {
    env.error(stringc
      << context << " are only valid for class member "
      << "functions (constructors in particular)",
      EF_DISAMBIGUATES);
    return NULL;
  }

  // make sure this function is a constructor; should already have
  // been mapped to the special name
  if (nameAndParams->var->name != env.constructorSpecialName) {
    env.error(stringc
      << context << " are only valid for constructors",
      EF_DISAMBIGUATES);
    return NULL;
  }

  return enclosing;
}


bool hasDependentActualArgs(FakeList<ArgExpression> *args)
{
  FAKELIST_FOREACH(ArgExpression, args, iter) {
    // <dependent> or TypeVariable or PseudoInstantiation
    if (iter->expr->type->containsGeneralizedDependent()) {
      return true;
    }
  }
  return false;
}


// cppstd 12.6.2 covers member initializers
void Function::tcheck_memberInits(Env &env)
{
  if (inits ||
      nameAndParams->var->name == env.constructorSpecialName) {
    // this should be a constructor
    CompoundType *enclosing = verifyIsCtor(env, "ctor member inits");

    // bhackett: disable. this can trip if there were tcheck/parse errors.
    // if (!enclosing) {
    //   return;
    // }

    // ok, so far so good; now go through and check the member inits
    // themselves
    FAKELIST_FOREACH_NC(MemberInit, inits, iter) {
      iter->tcheck(env, enclosing);
    }
  }
  else {
    // no inits and doesn't have a ctor name, skip
  }
}

void MemberInit::tcheck(Env &env, CompoundType *enclosing)
{
  // resolve template arguments in 'name'
  tcheckPQName(name, env, NULL /*scope*/, LF_NONE);

  // typecheck the arguments
  //
  // dsw: I do not want to typecheck the args twice, as it is giving
  // me problems, so I moved this
  //
  // 2005-05-28: (in/t0497.cc) Moved tchecking of arguments up above
  // place where we might bail due to dependent base class type, so
  // they will always be disambiguated.  This now invalidates dsw's
  // comments so we'll see if it causes problems.
  ArgumentInfoArray argInfo(args->count() + 1);
  args = tcheckArgExprList(args, env, argInfo);

  // bhackett: bail out if we don't know which class is being initialized.
  if (!enclosing)
    return;

  // check for a member variable, since they have precedence over
  // base classes [para 2]; member inits cannot have qualifiers
  if (!name->hasQualifiers()) {
    // look for the given name in the class; should be an immediate
    // member, not one that was inherited
    Variable *v = enclosing->lookup_one(name->getName(), env, LF_INNER_ONLY);

    // bhackett: member list initialization of anonymous struct/union fields.
    if (!v) {
      ArrayStack<Variable*> anon_fields;
      if (findAnonymousField(env, enclosing, name, anon_fields)) {
        // get the innermost field.
        v = anon_fields.pop();
        while (!anon_fields.isEmpty()) {
          v = anon_fields.pop();
        }
      }
    }

    if (v && !v->hasFlag(DF_TYPEDEF)) {     // typedef -> fall down to next area (in/t0390.cc)
      // only "nonstatic data member"
      if (v->hasFlag(DF_STATIC) ||
          v->type->isFunctionType()) {
        env.error("you can't initialize static data "
                  "nor member functions in a ctor member init list");
        return;
      }

      // annotate the AST
      member = env.storeVar(v);

      if (!hasDependentActualArgs(args)) {     // in/t0270.cc
        // decide which of v's possible constructors is being used
        ctorVar = env.storeVar(
          outerResolveOverload_ctor(env, env.loc(), v->type, argInfo));
        compareCtorArgsToParams(env, ctorVar, args, argInfo);
      }

      // TODO: check that the passed arguments are consistent
      // with at least one constructor of the variable's type.
      // dsw: update: isn't this what the assertion that ctorVar is
      // non-null is doing, since the call to
      // outerResolveOverload_ctor() will not succeed otherwise?

      // TODO: make sure that we only initialize each member once.
      // dsw: update: see below; do this in
      // cc_elaborate.cc:completeNoArgMemberInits()

      // TODO: provide a warning if the order in which the
      // members are initialized is different from their
      // declaration order, since the latter determines the
      // order of side effects.
      // dsw: update: this would have to be done in
      // cc_elaborate.cc:completeNoArgMemberInits(), since I re-order
      // the MemberInits there.

      return;
    }
  }

  // not a member name.. what about the name of base class?
  // since the base class initializer can use any name which
  // denotes the base class [para 2], first look up the name
  // in the environment generally
  //
  // 2005-04-17: in/k0054.cc: need LF_SELFNAME here
  //
  // TODO: get rid of LF_SELFNAME, or at least invert the sense,
  // so it is the default behavior
  Variable *baseVar = env.lookupPQ_one(name, LF_SELFNAME);
  if (baseVar &&
      baseVar->isType() &&
      baseVar->type->isCompoundType()) {
    // as expected
  }
  else if (baseVar &&
           baseVar->isType() &&
           baseVar->type->isGeneralizedDependent()) {
    // let it go
    return;
  }
  else {
    // complain
    env.error(stringc << "`" << *name << "' does not denote any class");
    return;
  }
  CompoundType *baseClass = baseVar->type->asCompoundType();

  // is this class a direct base, and/or an indirect virtual base?
  bool directBase = false;
  bool directVirtual = false;
  bool indirectVirtual = false;
  FOREACH_OBJLIST(BaseClass, enclosing->bases, baseIter) {
    BaseClass const *b = baseIter.data();

    // check for direct base
    if (b->ct == baseClass) {
      directBase = true;
      directVirtual = b->isVirtual;
    }

    // check for indirect virtual base by looking for virtual
    // base of a direct base class
    if (b->ct->hasVirtualBase(baseClass)) {
      indirectVirtual = true;
    }
  }

  // did we find anything?
  if (!directBase && !indirectVirtual) {
    // if there are qualifiers, then it can't possibly be an
    // attempt to initialize a data member
    char const *norData = name->hasQualifiers()? "" : ", nor a data member,";
    env.error(stringc
              << "`" << *name << "' is not a base class" << norData
              << " so it cannot be initialized here");
    return;
  }

  // check for ambiguity [para 2]
  if (directBase && !directVirtual && indirectVirtual) {
    env.error(stringc
              << "`" << *name << "' is both a direct non-virtual base, "
              << "and an indirect virtual base; therefore the initializer "
              << "is ambiguous (there's no quick fix--you have to change "
              << "your inheritance hierarchy or forego initialization)");
    return;
  }

  // annotate the AST
  base = baseClass;

  // TODO: verify correspondence between template arguments
  // in the initializer name and template arguments in the
  // base class list

  // TODO: check that the passed arguments are consistent
  // with the chosen constructor

  // determine which constructor is being called
  ctorVar = env.storeVar(
    outerResolveOverload_ctor(env, env.loc(),
                              baseVar->type,
                              argInfo));
  compareCtorArgsToParams(env, ctorVar, args, argInfo);
}


void Function::tcheck_handlers(Env &env)
{
  FAKELIST_FOREACH_NC(Handler, handlers, iter) {
    iter->tcheck(env);
  }
}


bool Function::instButNotTchecked() const
{            
  return !!cloneThunkSource;
}


// MemberInit

// if decl describes 'typedef some_type foo, *pfoo, **ppfoo', etc.
// then returns 'foo'. otherwise returns NULL.
StringRef GetTypedefName(Declaration *decl)
{
  if (decl->dflags & DF_TYPEDEF) {
    FakeList<Declarator> *decl_list = decl->decllist;
    while (decl_list != NULL) {
      IDeclarator *d = decl_list->first()->decl;
      decl_list = decl_list->butFirst();

      if (D_name *nd = d->ifD_name()) {
        PQName *name = nd->name;
        if (PQ_name *nname = name->ifPQ_name()) {
          return nname->name;
        }
      }
    }
  }

  return NULL;
}

// -------------------- Declaration -------------------
void Declaration::tcheck(Env &env, DeclaratorContext context)
{
  // if there are no declarators, the type specifier's tchecker
  // needs to know this (for e.g. 3.3.1 para 5)
  if (decllist->isEmpty() &&
      spec->isTS_elaborated() &&
      context != DC_TF_EXPLICITINST) {     // in/t0557.cc
    dflags |= DF_FORWARD;
  }

  // if we're declaring an anonymous type, give it a name.
  // try to give types the name assigned by a typedef if available.
  StringRef anonymous_name = false;

  if (spec->isTS_classSpec()) {
    TS_classSpec *cs = spec->asTS_classSpec();
    if (cs->name == NULL) {
      StringRef nname = GetTypedefName(this);
      if (nname == NULL) {
        nname = env.getAnonName(spec->loc, cs->keyword);
        anonymous_name = nname;
      }

      cs->name = new PQ_name(spec->loc, nname);
    }
  }
  if (spec->isTS_enumSpec()) {
    TS_enumSpec *es = spec->asTS_enumSpec();
    if (es->name == NULL) {
      es->name = GetTypedefName(this);
      if (es->name == NULL)
        es->name = env.getAnonName(spec->loc, TI_ENUM);
    }
  }

  // bhackett: disable warnings.
  /*
  // give warning for anonymous struct
  if (decllist->isEmpty() &&
      spec->isTS_classSpec() &&
      spec->asTS_classSpec()->name == NULL &&
      spec->asTS_classSpec()->keyword != TI_UNION) {
    if (env.lang.allowAnonymousStructs == B3_WARN) {
      env.warning(spec->loc, "anonymous structs are not legal in C++ "
                             "(gcc/msvc bug/extension allows it)");
    }
    else if (env.lang.allowAnonymousStructs == B3_FALSE) {
      // it's actually not an error yet, it is just useless, because
      // it cannot be used
      env.warning(spec->loc, "useless declaration");
    }
  }
  */

  // check the specifier in the prevailing environment
  Type *specType = spec->tcheck(env, dflags);

  // if this is an anonymous struct/union add it to the containing class.
  if (anonymous_name && decllist->isEmpty()) {
    xassert(spec->isTS_classSpec());

    Scope *scope = env.acceptingScope(DF_NONE);
    if (scope->curCompound != NULL) {
      // make a field with the same name as the struct/union. do not add
      // it to the scope itself (it cannot be referred to), but add it
      // to the dataMembers list.

      Variable *field = env.makeVariable(spec->loc, anonymous_name,
                                         specType, DF_MEMBER);
      field->scope = scope;
      scope->curCompound->dataMembers.append(field);
    }
    else {
      env.warning(spec->loc, "anonymous struct/union cannot be used");
    }
  }

  // ---- the following code is adopted from (the old) tcheckFakeExprList ----
  // (I couldn't just use the same code, templatized as necessary,
  // because I need my Declarator::Tcheck objects computed anew for
  // each declarator..)

  if (!decllist->isEmpty()) {
    // check first declarator
    Declarator::Tcheck dt1(specType, dflags, context);
    decllist = FakeList<Declarator>::makeList(decllist->first()->tcheck(env, dt1));

    // check subsequent declarators
    Declarator *prev = decllist->first();
    while (prev->next) {
      // some analyses don't want the type re-used, so let
      // the factory clone it if it wants to
      Type *dupType = specType;

      Declarator::Tcheck dt2(dupType, dflags, context);
      prev->next = prev->next->tcheck(env, dt2);

      prev = prev->next;
    }
  }

  // ---- end of code from tcheckFakeExprList ----
}


// -------------------- ASTTypeId -------------------
ASTTypeId *ASTTypeId::tcheck(Env &env, Tcheck &tc)
{
  if (!ambiguity) {
    mid_tcheck(env, tc);
    return this;
  }

  ASTTypeId *ret = resolveImplIntAmbig(env, this);
  if (ret) {
    return ret->tcheck(env, tc);
  }

  return resolveAmbiguity(this, env, "ASTTypeId", false /*priority*/, tc);
}

void ASTTypeId::mid_tcheck(Env &env, Tcheck &tc)
{
  if (spec->isTS_classSpec() && !spec->asTS_classSpec()->name) {
    // outside a declaration (that is, anyplace ASTTypeId occurs), gcc
    // does not do anonymous union or struct scope promotion, even in
    // C++ mode; so make up a name
    StringRef fakeName = env.getAnonName(spec->loc, spec->asTS_classSpec()->keyword);
    spec->asTS_classSpec()->name = new PQ_name(env.loc(), fakeName);
    TRACE("env", "substituted name " << fakeName <<
                 " in anon type at " << decl->getLoc());
  }

  // check type specifier
  Type *specType = spec->tcheck(env, DF_NONE);

  // pass contextual info to declarator
  Declarator::Tcheck dt(specType, tc.dflags, tc.context);
  
  xassert(!tc.newSizeExpr || tc.context == DC_E_NEW);

  // check declarator
  decl = decl->tcheck(env, dt);

  // retrieve add'l info from declarator's tcheck struct
  if (tc.newSizeExpr) {
    *(tc.newSizeExpr) = dt.size_E_new;
  }
}


Type *ASTTypeId::getType() const
{
  xassert(decl->var);
  return decl->var->type;
}


// ---------------------- PQName -------------------
void tcheckPQName(PQName *&name, Env &env, Scope *scope, LookupFlags lflags)
{
  if (!name->isPQ_qualifier()) {
    // easy case 1
    name->tcheck_pq(env, scope, lflags);
    return;
  }

  PQ_qualifier *qual = name->asPQ_qualifier();
  if (!qual->ambiguity) {
    // easy case
    qual->tcheck_pq(env, scope, lflags);
    return;
  }

  // make sure nothing changes the environment...
  int beforeChange = env.getChangeCount();

  // all of the ambiguous alternatives must be PQ_qualifiers with
  // template arguments, or PQ_templates; tcheck the first argument
  // of each one, and use that to disambiguate
  while (qual->ambiguity) {
    // tcheck first arg of 'qual', mostly discarding errors
    STemplateArgument sarg;
    {
      DisambiguationErrorTrapper trapper(env);
      qual->templArgs->tcheck(env, sarg);

      // discard errors (other than those saved in 'trapper')
      ErrorList discard;
      discard.takeMessages(env.errors);
    }

    // better not have changed the environment!
    xassert(env.getChangeCount() == beforeChange);

    if (sarg.hasValue()) {
      // this is the chosen one
      qual->ambiguity = NULL;
      name = qual;
      qual->tcheck_pq(env, scope, lflags);
      return;
    }

    // try next
    if (qual->ambiguity->isPQ_qualifier()) {
      qual = qual->ambiguity->asPQ_qualifier();
    }
    else {
      xassert(qual->ambiguity->isPQ_template());

      // since all preceding alternatives have failed, and PQ_template
      // does not have an 'ambiguity' pointer, select it and tcheck it
      name = qual->ambiguity;
      name->tcheck_pq(env, scope, lflags);
      return;
    }
  }

  // got to the end of the list, select+tcheck the final one
  name = qual;
  qual->tcheck_pq(env, scope, lflags);
}


// The given 'src' is a DAG of 'ambiguity' and 'next' links encoding
// all possible ways to interpret some syntax as a list of template
// arguments.  We must pick one such list and store the interpreted
// arguments in 'dest'.  The strategy is to check the arguments in
// order, and follow the 'next' link only of the chosen argument at
// each step.
bool tcheckTemplateArgumentList(ObjList<STemplateArgument> &dest,
                                TemplateArgument *&src, Env &env)
{
  bool ret = true;

  // normally I would expect 'dest' to be empty, but apparently we
  // sometimes tcheck PQNames more than once (maybe due to ambiguities
  // higher up?), and so I will just throw away any previous
  // results....
  dest.deleteAll();

  // keep track of the previous node in the list, so we can string
  // together the final disambiguated sequence
  TemplateArgument **prev = &src;

  TemplateArgument *ta = *prev;
  while (ta) {
    if (!ta->isTA_templateUsed()) {
      // disambiguate and check 'ta', putting its final result
      // into 'sarg'
      STemplateArgument *sarg = new STemplateArgument;
      ta = ta->tcheck(env, *sarg);
      if (!sarg->hasValue()) {
        ret = false;        // some kind of error
      }

      // remember 'sarg' (in wrong order, will fix below)
      dest.prepend(sarg);
    }

    // string up the chosen one
    xassert(ta->ambiguity == NULL);     // these links should all be cut now
    *prev = ta;

    // follow the 'next' link in 'ta', as it was the chosen one
    prev = &(ta->next);
    ta = *prev;
  }

  // fix the order of 'dest'
  dest.reverse();

  return ret;
}

void PQ_qualifier::tcheck_pq(Env &env, Scope *scope, LookupFlags lflags)
{
  if (!( lflags & LF_DECLARATOR )) {
    // no need to do scope association stuff
    tcheckTemplateArgumentList(sargs, templArgs, env);
    tcheckPQName(rest, env, scope, lflags);
    return;
  }

  // In a template declarator context, we want to stage the use of
  // the template parameters so as to ensure proper association
  // between parameters and qualifiers.  For example, if we have
  //
  //   template <class S>
  //   template <class T>
  //   int A<S>::foo(T *t) { ... }
  //
  // and we're about to tcheck "A<S>", the SK_TEMPLATE_PARAMS scope
  // containing T that is currently on the stack must be temporarily
  // removed so that the template arguments to A cannot see it.
  //
  // So, for this and other reasons, find the template argument or
  // parameter scope that corresponds to 'bareQualifierVar'.

  // begin by looking up the bare name, igoring template arguments
  Variable *bareQualifierVar = env.lookupOneQualifier_bareName(scope, this, lflags);

  // now check the arguments
  if (!tcheckTemplateArgumentList(sargs, templArgs, env)) {
    // error already reported; just finish up and bail
    tcheckPQName(rest, env, scope, lflags);
    return;
  }

  // scope that has my template params
  Scope *hasParamsForMe = NULL;

  if (!(lflags & LF_EXPLICIT_INST) &&            // not explicit inst request
      bareQualifierVar) {                        // lookup succeeded
    if (bareQualifierVar->isTemplate() &&          // names a template
        sargs.isNotEmpty()) {                      // arguments supplied
      // 14.7.3p5:
      //   - if all template args are concrete, and
      //   - they correspond to an explicit specialization
      //   - then "template <>" is *not* used (for that class)
      // t0248.cc tests a couple cases...
      bool hasVars = containsVariables(sargs);
      if (!hasVars &&
          bareQualifierVar->templateInfo()->getSpecialization(sargs)) {
        // do not associate 'bareQualifier' with any template scope
      }
      else {
        hasParamsForMe = env.findParameterizingScope(bareQualifierVar, hasVars);
      }
    }

    // Apparently, it is legal (as in, both GCC and ICC allow it) to
    // use a typedef to name an explicit specialization.  I think it's
    // a bit strange, as 14.7.3p17,18 seem to imply a syntactic
    // correlation between <> in template parameter lists and <> in
    // declarator-ids, and that correlation is broken if a typedef is
    // used.  In particular, the syntax could not also be used for a
    // *partial* specialization, since the parameters would not be
    // visible at the point the typedef is created.
    //
    // However, 7.1.3 seems to say that typedefs are allowed as
    // synonyms for their referents in any context except those
    // prohibited by 7.1.3p4, and this is not one of those.
    //
    // To implement this, I will try to determine how many levels of
    // template class implicit specializations are present between
    // 'bareQualifierVar' and 'scope', and associate each one
    // with a template parameter list.  (in/t0555.cc)
    if (bareQualifierVar->isExplicitTypedef() &&
        bareQualifierVar->type->isCompoundType() &&
        !bareQualifierVar->isTemplate(true /*considerInherited*/)) {
      // step 1: find all the classes below 'scope'
      SObjList<CompoundType> specs;
      int ct = 0;
      for (Scope *s = bareQualifierVar->getDenotedScope();
           s->isClassScope() && s != scope;
           s = mustBeNonNull(s->parentScope)) {
        specs.prepend(s->curCompound);        // want outermost first
        ct++;
      }

      // step 2: associate those that are implicit specializations
      SFOREACH_OBJLIST_NC(CompoundType, specs, iter) {
        TemplateInfo *ti = iter.data()->templateInfo();
        if (ti && ti->isInstantiation()) {    // aka implicit specialization
          Scope *paramScope = env.findParameterizingScope(ti->var, false /*hasVars*/);
          if (!paramScope) {
            // error already reported
          }
          else if (ct > 1) {
            paramScope->setParameterizedEntity(ti->var);

            TRACE("templateParams",
              "associated " << paramScope->desc() <<
              " with " << ti->var->fullyQualifiedName() <<
              " (found using typedef expansion)");
          }
          else {
            // this is the last element in the list, 'bareQualifierVar'
            // itself; don't associate it here; instead, stash it
            // in 'hasParamsForMe' and let the code below associate it
            xassert(ct == 1);
            xassert(iter.data() == bareQualifierVar->type->asCompoundType());
            hasParamsForMe = paramScope;

            TRACE("templateParams",
              "later, will associate " << paramScope->desc() <<
              " with " << ti->var->fullyQualifiedName() <<
              " (found using typedef expansion)");
          }
        }

        ct--;
      }
    }
  }

  // finish looking up this qualifier
  bool dependent;
  bool anyTemplates;        // will be ignored
  Scope *denotedScope = env.lookupOneQualifier_useArgs(
    bareQualifierVar,       // scope found w/o using args
    sargs,                  // template args
    dependent, anyTemplates, lflags);

  if (denotedScope && denotedScope->curCompound) {
    // must be a complete type [ref?] (t0245.cc)
    env.ensureCompleteType("use as qualifier",
      denotedScope->curCompound->typedefVar->type);

    if (hasParamsForMe) {
      // in/t0461.cc: My delegation scheme has a flaw, in that I set
      // a scope as 'delegated' before the thing that delegates to
      // it is on the scope stack, making the template parameters
      // effectively invisible for a short period.  This shows up in
      // an out-of-line ctor definition like A<T>::A<T>(...){}.  So
      // detect this, and as a hack, check the last bit of the name
      // *before* setting up the delegation.
      //
      // 2005-04-16: in/k0047.cc: generalize by doing this whenever
      // we're at the next-to-last component of the name
      if (!rest->isPQ_qualifier()) {
        tcheckPQName(rest, env, denotedScope, lflags);
      }

      // cement the association now
      hasParamsForMe->setParameterizedEntity(denotedScope->curCompound->typedefVar);

      TRACE("templateParams",
        "associated " << hasParamsForMe->desc() <<
        " with " << denotedScope->curCompound->instName);

      // if we already tcheck'd the final component above, bail now
      if (!rest->isPQ_qualifier()) {
        return;
      }
    }
  }

  tcheckPQName(rest, env, denotedScope, lflags);
}

void PQ_name::tcheck_pq(Env &env, Scope *, LookupFlags)
{}

void PQ_operator::tcheck_pq(Env &env, Scope *, LookupFlags)
{
  o->tcheck(env);
}

void PQ_template::tcheck_pq(Env &env, Scope *, LookupFlags lflags)
{                             
  tcheckTemplateArgumentList(sargs, templArgs, env);
}


// -------------- "dependent" name stuff ---------------
// This section has a few functions that are common to the AST
// nodes that have to deal with dependent name issues.  (14.6.2)

// lookup has found 'var', and we might want to stash it
// in 'nondependentVar' too
void maybeNondependent(Env &env, SourceLoc loc, Variable *&nondependentVar,
                       Variable *var)
{
  if (!var->hasFlag(DF_TYPEDEF) && var->type->isGeneralizedDependent()) {
    // if this was the name of a variable, but the type refers to some
    // template params, then this shouldn't be considered
    // non-dependent (t0276.cc)
    //
    // TODO: this can't be right... there is still a fundamental
    // flaw in how I regard names whose lookup is nondependent but
    // the thing they look up to is dependent
    return;
  }

  if (!var->scope && !var->isTemplateParam()) {
    // I'm pretty sure I don't need to remember names that are not
    // in named scopes, other than template params themselves (t0277.cc)
    return;
  }

  if (env.inUninstTemplate() &&               // we're in a template
      !var->type->isSimple(ST_DEPENDENT) &&   // lookup was non-dependent
      !var->type->isDependentQType() &&       //   (also would be dependent)
      !var->type->isError() &&                // and not erroneous
      !var->isMemberOfTemplate()) {           // will be in scope in instantiation
    TRACE("dependent", toString(loc) << ": " <<
                       (nondependentVar? "replacing" : "remembering") <<
                       " non-dependent lookup of `" << var->name <<
                       "' found var at " << toString(var->loc));
    nondependentVar = var;
  }
}

// if we want to re-use 'nondependentVar', return it; otherwise return NULL
Variable *maybeReuseNondependent(Env &env, SourceLoc loc, LookupFlags &lflags,
                                 Variable *nondependentVar)
{
  // should I use 'nondependentVar'?
  if (nondependentVar && !env.inUninstTemplate()) {
    if (nondependentVar->isTemplateParam()) {
      // We don't actually want to use 'nondependentVar', because that
      // Variable was only meaningful to the template definition.  Instead
      // we want the *corresponding* Variable that is now bound to a
      // template argument, and LF_TEMPL_PARAM will find it (and skip any
      // other names).
      TRACE("dependent", toString(loc) <<
                         ": previously-remembered non-dependent lookup for `" <<
                         nondependentVar->name << "' was a template parameter");
      lflags |= LF_TEMPL_PARAM;
    }
    else {
      // use 'nondependentVar' directly
      TRACE("dependent", toString(loc) <<
                         ": using previously-remembered non-dependent lookup for `" <<
                         nondependentVar->name << "': at " <<
                         toString(nondependentVar->loc));
      return nondependentVar;
    }
  }

  // do the lookup without using 'nondependentVar'
  return NULL;
}


// --------------------- TypeSpecifier --------------
Type *TypeSpecifier::tcheck(Env &env, DeclFlags dflags)
{
  env.setLoc(loc);

  Type *t = itcheck(env, dflags);
  Type *ret = env.tfac.applyCVToType(loc, cv, t, this);
  if (!ret) {
    if (t->isFunctionType() && env.lang.allowCVAppliedToFunctionTypes) {
      env.diagnose3(env.lang.allowCVAppliedToFunctionTypes, loc,
                    "cannot apply const/volatile to function types (gcc bug allows it)");
      return t;    // ignore the cv-flags
    }
    else {
      return env.error(t, stringc
        << "cannot apply const/volatile to type `" << t->toString() << "'");
    }
  }
  return ret;
}


// does 'name' begin with 'qualifier' and end with 'name'?
bool isTwoPartName(Env &env, PQName *name,
                   char const *qualifier, char const *final)
{
  if (!name->isPQ_qualifier()) {
    return false;
  }

  StringRef q = name->asPQ_qualifier()->qualifier;
  StringRef f = name->getName();

  if (q == env.str(qualifier) && f == env.str(final)) {
    return true;
  }
  else {
    return false;
  }
}


// This function recognizes a PQName that comes from a buggy gcc-2
// header and in that context is intended to name a dependent type.
//
// forms recognized:
//   g0024.cc: __default_alloc_template<__threads, __inst>::_Obj
//   g0026.cc: basic_string <charT, traits, Allocator>::Rep
//   g0026.cc: basic_string <charT, traits, Allocator>::size_type
bool isBuggyGcc2HeaderDQT(Env &env, PQName *name)
{
  if (isTwoPartName(env, name, "__default_alloc_template", "_Obj") ||
      isTwoPartName(env, name, "basic_string", "Rep") ||
      isTwoPartName(env, name, "basic_string", "size_type")) {
    return true;
  }

  return false;
}


// 7.1.5.2
Type *TS_name::itcheck(Env &env, DeclFlags dflags)
{
  tcheckPQName(name, env, NULL /*scope*/, LF_NONE);

  ErrorFlags eflags = EF_NONE;
  LookupFlags lflags = LF_EXPECTING_TYPE;

  // should I use 'nondependentVar'?
  Variable *v = maybeReuseNondependent(env, loc, lflags, nondependentVar);
  if (v) {
    var = v;
    return var->type;
  }

  if (typenameUsed) {
    if (!name->hasQualifiers()) {
      // cppstd 14.6 para 5, excerpt:
      //   "The keyword typename shall only be applied to qualified
      //    names, but those names need not be dependent."
      env.error("the `typename' keyword can only be used with a qualified name");
    }

    lflags |= LF_TYPENAME;
  }
  else {
    // if the user uses the keyword "typename", then the lookup errors
    // are non-disambiguating, because the syntax is unambiguous;
    // otherwise, they are disambiguating (which is the usual case)
    eflags |= EF_DISAMBIGUATES;
  }

  if (!env.lang.isCplusplus) {
    // in C, we never look at a class scope unless the name is
    // preceded by "." or "->", which it certainly is not in a TS_name
    // (in/c/dC0013.c)
    lflags |= LF_SKIP_CLASSES;
  }

  // hack, until LF_SELFNAME becomes the default and I fix the
  // problems in Env::applyPQNameTemplateArguments: if the name
  // does not have template arguments, make the self-name visible
  if (!name->getUnqualifiedName()->isPQ_template()) {
    lflags |= LF_SELFNAME;
  }

do_lookup:
  v = env.lookupPQ_one(name, lflags);

  // gcc-2 hack
  if (!v &&
      env.lang.gcc2StdEqualsGlobalHacks &&
      isTwoPartName(env, name, "std", "string")) {
    // try looking it up in global scope
    v = env.lookupPQ_one(name->getUnqualifiedName(), lflags);
  }

  if (!v) {
    // a little diagnostic refinement: if the only problem is with the
    // template arguments, but the name would be a type if the args
    // were ok, don't call it disambiguating (in/t0454.cc, error 1)
    if (name->isPQ_template()) {
      Variable *primary = env.lookupPQ_one(name, lflags | LF_TEMPL_PRIMARY);
      if (primary && primary->isType() && primary->isTemplate()) {
        eflags &= ~EF_DISAMBIGUATES;
      }
    }

    // NOTE:  Since this is marked as disambiguating, but the same
    // error message in E_variable::itcheck is not marked as such, it
    // means we prefer to report the error as if the interpretation as
    // "variable" were the only one.
    return env.error(stringc
      << "there is no type called `" << *name << "'", eflags);
  }

  if (!v->hasFlag(DF_TYPEDEF)) {
    if (v->type && v->type->isSimple(ST_DEPENDENT)) {
      // is this a gcc-2 header bug? (in/gnu/g0024.cc)
      if (env.lang.allowGcc2HeaderSyntax &&
          isBuggyGcc2HeaderDQT(env, name)) {
        env.diagnose3(env.lang.allowGcc2HeaderSyntax, name->loc,
                      stringc << "dependent type name `" << *name
                              << "' requires 'typename' keyword (gcc-2 bug allows it)");
        lflags |= LF_TYPENAME;
        goto do_lookup;
      }
      else {
        // more informative error message (in/d0111.cc, error 1)
        return env.error(stringc
          << "dependent name `" << *name
          << "' used as a type, but the 'typename' keyword was not supplied", eflags);
      }
    }
    else {
      return env.error(stringc
        << "variable name `" << *name << "' used as if it were a type", eflags);
    }
  }

  // TODO: access control check

  var = env.storeVar(v);    // annotation

  // should I remember this non-dependent lookup?
  maybeNondependent(env, loc, nondependentVar, var);

  // 7/27/04: typedefAliases used to be maintained at this point, but
  // now it is gone

  // there used to be a call to applyCV here, but that's redundant
  // since the caller (tcheck) calls it too
  return var->type;
}


Type *TS_simple::itcheck(Env &env, DeclFlags dflags)
{ 
  // This is the one aspect of the implicit-int solution that cannot
  // be confined to implint.h: having selected an interpretation that
  // uses implicit int, change it to ST_INT so that analyses don't
  // have to know about any of this parsing nonsense.
  if (id == ST_IMPLINT) {
    // 2005-04-07: I had been doing the following:
    //   id = ST_INT;      
    // but the problem with that is that there are cases (e.g.,
    // in/c/k0008.c) where a single TS_simple will appear in more than
    // one context.  If the first context's tcheck changes 'id' as
    // above, and the second context is ambiguous, the second context
    // won't know that it was ST_IMPLINT and will therefore fail to
    // resolve it properly.
    //
    // So my new solution is to *only* put ST_INT into the 'type',
    // leaving ST_IMPLINT in the 'id' field so later tchecks can see
    // that it was using implicit-int.  Client analyses should be
    // unaffected, since they should be looking at 'type', not 'id'.
    return env.getSimpleType(ST_INT, cv);
  }

  return env.getSimpleType(id, cv);
}


// This function maps syntax like
//
//   "class A"                            // ordinary class
//   "class A<int>"                       // existing instantiation or specialization
//   "template <class T> class A"         // template class decl
//   "template <class T> class A<T*>"     // partial specialization decl
//   "template <> class A<int>"           // complete specialization decl
//
// to a particular CompoundType.  If there are extant template
// parameters, then 'templateParams' will be set below to non-NULL
// (but possibly empty).  If the name has template arguments applied
// to it, then 'templateArgs' will be non-NULL.
//
// There are three syntactic contexts for this, identified by the
// 'dflags' present.  Within each of these I categorize w.r.t. the
// presence of template parameters and arguments:
//
//   "class A ;"          // DF_FORWARD=1  DF_DEFINITION=0
//
//     no-params no-args    ordinary forward declaration
//     params    no-args    fwd decl of template primary
//     no-params args       old-style explicit instantiation request [ref?]
//     params    args       fwd decl of explicit specialization
//
//   "class A *x ;"       // DF_FORWARD=0  DF_DEFINITION=0
//
//     no-params no-args    fwd decl, but might push into outer scope (3.3.1 para 5)
//     params    no-args    illegal [ref?]
//     no-params args       use of a template instantiation or specialization
//     params    args       illegal
//
//   "class A { ... } ;"  // DF_FORWARD=0  DF_DEFINITION=1
//
//     no-params no-args    ordinary class definition
//     params    no-args    template primary definition
//     no-params args       illegal
//     params    args       template specialization definition
//
// Note that the first and third cases are fairly parallel, one being
// a declaration and the other a definition.  The second case is the
// odd one out, though it is more like case 1 than case 3.  It is also
// quite rare, as such uses are almost always written without the
// "class" keyword.
CompoundType *checkClasskeyAndName(
  Env &env,
  Scope *scope,              // scope in which decl/defn appears
  SourceLoc loc,             // location of type specifier
  DeclFlags dflags,          // syntactic and semantic declaration modifiers
  TypeIntr keyword,          // keyword used
  PQName *name)              // name, with qualifiers and template args (if any)
{
  // bhackett: we should already have assigned a name for this type,
  // even if it is anonymous.
  xassert(name);

  // context flags
  bool forward = (dflags & DF_FORWARD);
  bool definition = (dflags & DF_DEFINITION);
  xassert(!( forward && definition ));

  // handle 'friend' the same way I do other case 2 decls, even though
  // that isn't quite right
  if (dflags & DF_FRIEND) {
    if (definition) {
      // 11.4p2
      env.error("you cannot define a class in a friend definitions");
      return NULL;
    }
    forward = false;
  }

  // template params?
  SObjList<Variable> *templateParams =
    scope->isTemplateParamScope()? &(scope->templateParams) : NULL;

  // template args?
  ObjList<STemplateArgument> *templateArgs = NULL;

  PQName *unqual = name->getUnqualifiedName();
  if (unqual->isPQ_template()) {
    // get the arguments
    templateArgs = &(unqual->asPQ_template()->sargs);
  }

  // indicate when a particular gcc-2 hack is being used...
  bool gcc2hack_explicitSpec = false;

  // reject illegal combinations
  if (!forward && !definition && templateParams) {
    // Actually, this requirement holds regardless of whether there is
    // a definition, but 'forward' only signals the presence of
    // declarators in non-definition cases.  So this error should be
    // caught elsewhere.  The code below will not run into trouble in
    // this case, so just let it go.
    //return env.error("templatized class declarations cannot have declarators");
  }
  if (definition && !templateParams && templateArgs) {
    if (env.lang.allowGcc2HeaderSyntax &&
        name->getName() == env.str("string_char_traits")) {
      env.diagnose3(env.lang.allowGcc2HeaderSyntax, name->loc,
                    "explicit class specialization requires \"template <>\" (gcc-2 bug allows it)");
      gcc2hack_explicitSpec = true;
                    
      // pretend we saw "template <>"
      templateParams = new SObjList<Variable>;    // will be leaked
    }
    else {
      env.error("class specifier name can have template arguments "
                "only in a templatized definition");
      return NULL;
    }
  }
  if (templateParams && templateParams->isEmpty() && !templateArgs) {
    env.error("complete specialization (\"<>\") requires template args");
    return NULL;
  }

  // bhackett: template unions are allowed by gcc.
  /*
  if (keyword==TI_UNION && (templateParams || templateArgs)) {
    env.error("template unions are not allowed");
    return NULL;
  }
  */

  // see if the environment already has this name
  CompoundType *ct = NULL;

  // decide how the lookup should be performed
  LookupFlags lflags = LF_ONLY_TYPES;     // 3.4.4p2,3
  if (!name->hasQualifiers() && (forward || definition)) {
    lflags |= LF_INNER_ONLY;
  }
  if (templateParams) {
    lflags |= LF_TEMPL_PRIMARY;
  }
  if (!env.lang.isCplusplus) {
    // in C mode, it is ok to have a typedef and a struct with the
    // same name (in/c/dC0023.cc)
    lflags |= LF_QUERY_TAGS;
  }

  // I need this for in/t0492.cc; this brings me one step closer
  // to making this flag be on by default
  lflags |= LF_SELFNAME;

  // do the lookup
  if (dflags & DF_DEFINITION) {
    // this is a lookup of the declarator-like type tag of a class
    // definition; the qualifier scopes have already been pushed
    // by my caller, so just look in the innermost scope
    ct = env.lookupCompound(name->getName(), lflags | LF_INNER_ONLY);
  }
  else {
    // this is a lookup of a use; see if the new mechanism can
    // handle it
    Variable *tag = env.lookupPQ_one(name, lflags);
    if (tag) {
      if (tag->type->isCompoundType()) {
        if (env.lang.isCplusplus && !tag->hasAnyFlags(DF_IMPLICIT | DF_SELFNAME)) {
          // found a user-introduced (not implicit) typedef, which
          // is illegal (3.4.4p2,3; 7.1.5.3p2)
          env.error(stringc << "`" << *name << "' is a typedef-name, "
                    << "so cannot be used after '" 
                    << toString(keyword) << "'");
          return NULL;
        }
        ct = tag->type->asCompoundType();
      } 
      else if (tag->type->isGeneralizedDependent()) {
        return NULL;
      }
      else {
        env.error(tag->type, stringc 
                  << "`" << *name << "' is not a struct/class/union");
        return NULL;
      }
    }
  }

  // failed lookup is cause for immediate abort in a couple of cases
  if (!ct &&
      (name->hasQualifiers() || templateArgs)) {
    env.error(stringc << "no such " << toString(keyword)
              << ": `" << *name << "'");
    return NULL;
  }

  CompoundType *primary = ct;       // used for specializations

  // if we have template args and params, refine 'ct' down to the
  // specialization of interest (if already declared)
  if (templateParams && templateArgs) {
    // this is supposed to be a specialization
    TemplateInfo *primaryTI = primary->templateInfo();
    if (!primaryTI) {
      env.error("attempt to specialize a non-template");
      return NULL;
    }

    // does this specialization already exist?
    Variable *spec = primaryTI->getSpecialization(*templateArgs);
    if (spec) {
      ct = spec->type->asCompoundType();
    }
    else {
      // did we already start to make an implicit instantiation
      // for these arguments?  (in/t0522.cc)
      spec = env.findInstantiation(primaryTI, *templateArgs);
      if (spec) {
        ct = spec->type->asCompoundType();
        if (ct->forward) {
          // body not yet instantiated, we're ok
          TRACE("template", "changing " << ct->instName << 
                            " from implicit inst to explicit spec");
          spec->templateInfo()->changeToExplicitSpec();
        }
        else {
          // cppstd 14.7.3p6
          env.error(stringc
            << ct->instName << " has already been implicitly instantiated, "
            << "so it's too late to provide an explicit specialization");
          return NULL;
        }
      }
      else {
        ct = NULL;
      }
    }
  }

  // if already declared, compare to that decl
  if (ct) {
    // check that the keywords match
    if ((int)ct->keyword != (int)keyword) {
      // it's ok for classes and structs to be confused (7.1.5.3 para 3)
      if ((keyword==TI_UNION) != (ct->keyword==CompoundType::K_UNION)) {
        env.error(stringc
          << "there is already a " << ct->keywordAndName()
          << ", but here you're defining a " << toString(keyword)
          << " " << *name);
        return NULL;
      }

      // let the definition keyword (of a template primary only)
      // override any mismatching prior decl
      if (definition && !templateArgs) {
        TRACE("env", "changing " << ct->keywordAndName() <<
                     " to a " << toString(keyword) << endl);
        ct->keyword = (CompoundType::Keyword)keyword;
      }
    }

    // do this before setting 'forward', so that inside
    // 'verifyCompatibleTemplateParameters' I can tell whether the
    // old declaration was a definition or not (in/k0022.cc)
    if (!templateParams && templateArgs) {
      // this is more like an instantiation than a declaration
    }
    else {
      // check correspondence between extant params and params on 'ct'
      env.verifyCompatibleTemplateParameters(scope, ct);
    }

    // definition of something previously declared?
    if (definition) {
      if (ct->templateInfo()) {
        // update the defnScope; this is important for out-of-line definitions
        // of nested classes, especially template classes
        TemplateInfo *ti = ct->templateInfo();
        Scope *defnScope = scope;
        while (defnScope->isTemplateParamScope()) {
          defnScope = defnScope->parentScope;
        }
        ti->defnScope = defnScope;

        TRACE("template", "template class " <<
                          (templateArgs? "specialization " : "") <<
                          "definition: " << ti->templateName() <<
                          ", defnScope is " << defnScope->desc());
      }

      if (ct->forward) {
        // now it is no longer a forward declaration
        ct->forward = false;
      }
      else {
        // bhackett: making this a warning. this shows up in linux
        // when separate typedef and struct definitions share the
        // same name (weird!).
        env.warning(stringc << ct->keywordAndName() << " has already been defined");
      }
    }
  }

  // if not already declared, make a new CompoundType
  else {
    // get the raw name for use in creating the CompoundType.
    // make up a name if it is anonymous.
    StringRef stringName = name->getName();

    // making an ordinary compound, or a template primary?
    if (!templateArgs) {
      Scope *destScope = (forward || definition) ?
        // if forward=true, 3.3.1 para 5 says:
        //   the elaborated-type-specifier declares the identifier to be a
        //   class-name in the scope that contains the declaration
        // if definition=true, I think it works the same [ref?]
        env.typeAcceptingScope() :
        // 3.3.1 para 5 says:
        //   the identifier is declared in the smallest non-class,
        //   non-function-prototype scope that contains the declaration
        env.outerScope() ;

      // this sets the parameterized primary of the scope
      env.makeNewCompound(ct, destScope, stringName, loc, keyword,
                          !definition /*forward*/);

      if (templateParams) {
        TRACE("template", "template class " << (definition? "defn" : "decl") <<
                          ": " << ct->templateInfo()->templateName());
      }
    }

    // making a template specialization
    else {
      SObjList<STemplateArgument> const &ssargs = objToSObjListC(*templateArgs);

      // make a new type, since a specialization is a distinct template
      // [cppstd 14.5.4 and 14.7]; but don't add it to any scopes
      env.makeNewCompound(ct, NULL /*scope*/, stringName, loc, keyword,
                          !definition /*forward*/);

      if (gcc2hack_explicitSpec) {
        // we need to fake a TemplateInfo
        ct->setTemplateInfo(new TemplateInfo(loc));
      }

      // dsw: need to register it at least, even if it isn't added to
      // the scope, otherwise I can't print out the name of the type
      // because at the top scope I don't know the scopeKind
      env.typeAcceptingScope()->registerVariable(ct->typedefVar);

      // similarly, the parentScope should be set properly
      env.setParentScope(ct);

      // 'makeNewCompound' will already have put the template *parameters*
      // into 'specialTI', but not the template arguments
      TemplateInfo *ctTI = ct->templateInfo();
      ctTI->copyArguments(ssargs);
      
      // fix the self-type arguments (only if partial inst)
      if (ct->selfType->isPseudoInstantiation()) {
        PseudoInstantiation *selfTypePI = ct->selfType->asPseudoInstantiation();
        selfTypePI->args.deleteAll();
        copyTemplateArgs(selfTypePI->args, ssargs);
      }

      // synthesize an instName to aid in debugging
      ct->instName = env.str(stringc << ct->name << sargsToString(ctTI->arguments));

      // add this type to the primary's list of specializations; we are not
      // going to add 'ct' to the environment, so the only way to find the
      // specialization is to go through the primary template
      TemplateInfo *primaryTI = primary->templateInfo();
      primaryTI->addSpecialization(ct->getTypedefVar());

      // the template parameters parameterize the specialization primary
      //
      // 8/09/04: moved this below 'makeNewCompound' so the params
      // aren't regarded as inherited
      if (!gcc2hack_explicitSpec) {
        scope->setParameterizedEntity(ct->typedefVar);
      }

      TRACE("template", (definition? "defn" : "decl") <<
                        " of specialization of template class " <<
                        primary->typedefVar->fullyQualifiedName() <<
                        ", " << ct->instName);
    }

    // record the definition scope, for instantiation to use
    if (templateParams && definition) {
      ct->templateInfo()->defnScope = env.nonTemplateScope();
    }
  }

  return ct;
}


Type *TS_elaborated::itcheck(Env &env, DeclFlags dflags)
{
  env.setLoc(loc);

  tcheckPQName(name, env, NULL /*scope*/, LF_NONE);

  if (keyword == TI_ENUM) {
    Variable *tag = env.lookupPQ_one(name, LF_ONLY_TYPES);
    if (!tag) {
      if (!env.lang.allowIncompleteEnums ||
          name->hasQualifiers()) {
        return env.error(stringc << "there is no enum called `" << *name << "'",
                         EF_DISAMBIGUATES);
      }
      else {
        // make a forward-declared enum (gnu/d0083.c)
        EnumType *et = new EnumType(name->getName());
        return env.declareEnum(loc, et);
      }
    }
    xassert(tag->isType());      // ensured by LF_ONLY_TYPES
    
    if (!tag->type->isEnumType()) {
      return env.error(stringc << "`" << *name << "' is not an enum");
    }
    if (!tag->hasFlag(DF_IMPLICIT)) {
      // found a user-introduced (not implicit) typedef, which
      // is illegal (3.4.4p2,3)
      return env.error(stringc << "`" << *name << "' is a typedef-name, "
                               << "so cannot be used after 'enum'");
    }
    EnumType *et = tag->type->asCVAtomicType()->atomic->asEnumType();

    this->atype = et;          // annotation
    return env.makeType(et);
  }
                                     
  CompoundType *ct =
    checkClasskeyAndName(env, env.scope(), loc, dflags, keyword, name);
  if (!ct) {
    ct = env.errorCompoundType;
  }

  this->atype = ct;              // annotation

  return ct->typedefVar->type;
}

                            
// typecheck declarator name 'name', pushing the sequence of scopes
// that necessary to tcheck what follows, and also returning that
// sequence in 'qualifierScopes' so the caller can undo it
void tcheckDeclaratorPQName(Env &env, ScopeSeq &qualifierScopes,
                            PQName *name, LookupFlags lflags)
{
  lflags |= LF_DECLARATOR;

  if (name) {
    // tcheck template arguments
    tcheckPQName(name, env, NULL /*scope*/, lflags);

    // lookup the name minus the final component; this is the scope
    Variable *scopeVar = env.lookupPQ_one(name, LF_GET_SCOPE_ONLY | lflags);
    
    // if that worked, get that scope and its parents, up to the current
    // innermost scope
    if (scopeVar) {
      env.getParentScopes(qualifierScopes, scopeVar);
    }

    // and push that sequence
    env.extendScopeSeq(qualifierScopes);
  }
}


Type *TS_classSpec::itcheck(Env &env, DeclFlags dflags)
{
  env.setLoc(loc);
  dflags |= DF_DEFINITION;

  // if we're on the second pass, then skip almost everything
  if (env.secondPassTcheck) {
    // just get the function bodies
    env.extendScope(ctype);
    tcheckFunctionBodies(env);
    env.retractScope(ctype);
    return ctype->typedefVar->type;
  }

  // scope in which decl appears; I save this now, before extending
  // it with qualifier scopes, for cases like in/t0441a.cc
  Scope *scope = env.scope();

  // lookup and push scopes in the name, if any
  ScopeSeq qualifierScopes;
  tcheckDeclaratorPQName(env, qualifierScopes, name, LF_NONE);

  // figure out which class the (keyword, name) pair refers to
  CompoundType *ct =
    checkClasskeyAndName(env, scope, loc, dflags, keyword, name);
  if (!ct) {
    // error already reported
    env.retractScopeSeq(qualifierScopes);
    this->ctype = env.errorCompoundType;
    return this->ctype->typedefVar->type;
  }

  this->ctype = ct;           // annotation

  // check the body of the definition
  tcheckIntoCompound(env, dflags, ct);

  env.retractScopeSeq(qualifierScopes);

  return ct->typedefVar->type;
}


// type check once we know what 'ct' is; this is also called
// to check newly-cloned AST fragments for template instantiation
void TS_classSpec::tcheckIntoCompound(
  Env &env, DeclFlags dflags,    // as in tcheck
  CompoundType *ct)              // compound into which we're putting declarations
{
  // should have set the annotation by now
  xassert(ctype);

  // are we an inner class?
  CompoundType *containingClass = env.acceptingScope()->curCompound;
  if (env.lang.noInnerClasses) {
    // nullify the above; act as if it's an outer class
    containingClass = NULL;
  }

  // let me map from compounds to their AST definition nodes
  ct->syntax = this;

  // only report serious errors while checking the class,
  // in the absence of actual template arguments
  DisambiguateOnlyTemp disOnly(env, ct->isTemplate() /*disOnly*/);

  // we should not be in an ambiguous context, because that would screw
  // up the environment modifications; if this fails, it could be that
  // you need to do context isolation using 'DisambiguateNestingTemp'
  xassert(env.disambiguationNestingLevel == 0);

  // 9/21/04: d0102.cc demonstrates that certain errors that are
  // marked 'disambiguating' can still be superfluous because of being
  // in uninstantiated template code.  So I'm going to use a big
  // hammer here, and throw away all non-EF_STRONG errors once
  // tchecking of this template finishes.  For the moment, that means
  // I need to save the existing errors.
  //
  // The filtering only happens when the "permissive" tracing flag
  // is set.
  UninstTemplateErrorFilter errorFilter(env);

  // open a scope, and install 'ct' as the compound which is
  // being built; in fact, 'ct' itself is a scope, so we use
  // that directly
  //
  // 8/19/04: Do this before looking at the base class specs, because
  // any prevailing template params are now attached to 'ct' and hence
  // only visible there (t0271.cc).
  env.extendScope(ct);

  // look at the base class specifications
  if (bases) {
    FAKELIST_FOREACH_NC(BaseClassSpec, bases, iter) {
      // resolve any template arguments in the base class name
      tcheckPQName(iter->name, env, NULL /*scope*/, LF_NONE);

      // cppstd 10, para 1: ignore non-types when looking up
      // base class names
      Variable *baseVar = env.lookupPQ_one(iter->name, LF_ONLY_TYPES);
      if (!baseVar) {
        env.error(stringc
          << "no class called `" << *(iter->name) << "' was found",
          EF_NONE);
        continue;
      }
      xassert(baseVar->hasFlag(DF_TYPEDEF));    // that's what LF_ONLY_TYPES means

      // special case for template parameters
      if (baseVar->type->isTypeVariable() ||
          baseVar->type->isPseudoInstantiation() ||
          baseVar->type->isDependentQType()) {
        // let it go.. we're doing the pseudo-check of a template;
        // but there's nothing we can add to the base class list,
        // and it wouldn't help even if we could, so do nothing
        TemplateInfo *ti = ct->templateInfo();
        ti->dependentBases.append(baseVar->type);
        continue;
      }

      // cppstd 10, para 1: must be a class type
      CompoundType *base = baseVar->type->ifCompoundType();
      if (!base) {
        env.error(stringc
          << "`" << *(iter->name) << "' is not a class or "
          << "struct or union, so it cannot be used as a base class");
        continue;
      }

      // also 10 para 1: must be complete type
      if (!env.ensureCompleteType("use as base class", baseVar->type)) {
        continue;
      }

      // fill in the default access mode if the user didn't provide one
      // [cppstd 11.2 para 2]
      AccessKeyword acc = iter->access;
      if (acc == AK_UNSPECIFIED) {
        acc = (ct->keyword==CompoundType::K_CLASS? AK_PRIVATE : AK_PUBLIC);
      }                                  
      
      // add this to the class's list of base classes
      ct->addBaseClass(new BaseClass(base, acc, iter->isVirtual));
      
      // annotate the AST with the type we found
      iter->type = base;
    }

    // we're finished constructing the inheritance hierarchy
    if (tracingSys("printHierarchies")) {
      string h1 = ct->renderSubobjHierarchy();
      cout << "// ----------------- " << ct->name << " -------------------\n";
      cout << h1;

      // for debugging; this checks that the 'visited' flags are being
      // cleared properly, among other things
      string h2 = ct->renderSubobjHierarchy();
      if (!h1.equals(h2)) {
        xfailure("second rendering doesn't match first");
      }
    }
  }

  // look at members: first pass is to enter them into the environment
  {
    // don't check function bodies
    Restorer<bool> r(env.checkFunctionBodies, false);

    FOREACH_ASTLIST_NC(Member, members->list, iter) {
      Member *member = iter.data();
      member->tcheck(env);
    }
  }

  // 2005-02-17: check default arguments first so they are available
  // to all function bodies (hmmm... what if a default argument
  // expression invokes a function that itself has default args,
  // but appears later in the file?  how could that ever be handled
  // cleanly?)
  //
  // 2005-02-18: Do this here instead of in 'tcheckFunctionBodies'
  // for greater uniformity with template instantiation.  Also, must
  // do it above 'addCompilerSuppliedDecls', since the presence of
  // default args affects whether (e.g.) a copy ctor exists.
  {
    DefaultArgumentChecker checker(env, ct->isInstantiation());
    
    // 2005-05-28: start with 'members' instead of 'this', to skip
    // around the prune in visitTypeSpecifier
    members->traverse(checker);
  }

  // default ctor, copy ctor, operator=; only do this for C++.
  if (env.lang.isCplusplus) {
    addCompilerSuppliedDecls(env, loc, ct);
  }

  // let the CompoundType build additional indexes if it wants
  ct->finishedClassDefinition(env.conversionOperatorName);

  // second pass: check function bodies
  // (only if we're not in a context where this is supressed)
  if (env.checkFunctionBodies) {
    tcheckFunctionBodies(env);
  }

  // now retract the class scope from the stack of scopes; do
  // *not* destroy it!
  env.retractScope(ct);

  if (containingClass) {
    // set the constructed scope's 'parentScope' pointer now that
    // we've removed 'ct' from the Environment scope stack; future
    // (unqualified) lookups in 'ct' will thus be able to see
    // into the containing class [cppstd 3.4.1 para 8]
    ct->parentScope = containingClass;
  }

  env.addedNewCompound(ct);
}


// This is pass 2 of tchecking a class.  It implements 3.3.6 para 1
// bullet 1, which specifies that the scope of a class member includes
// all function bodies.  That means that we have to wait until all
// the members have been added to the class scope before checking any
// of the function bodies.  Pass 1 does the former, pass 2 the latter.
void TS_classSpec::tcheckFunctionBodies(Env &env)
{ 
  xassert(env.checkFunctionBodies);

  CompoundType *ct = env.scope()->curCompound;
  xassert(ct);

  // inform the members that they are being checked on the second
  // pass through a class definition
  Restorer<bool> r(env.secondPassTcheck, true);
  
  // check function bodies and elaborate ctors and dtors of member
  // declarations
  FOREACH_ASTLIST_NC(Member, members->list, iter) {
    Member *member = iter.data();
    member->tcheck(env);
  }
}


Type *TS_enumSpec::itcheck(Env &env, DeclFlags dflags)
{
  env.setLoc(loc);

  EnumType *et = NULL;
  Type *ret = NULL;

  if (env.lang.allowIncompleteEnums && name) {
    // is this referring to an existing forward-declared enum?
    et = env.lookupEnum(name, LF_INNER_ONLY);
    if (et) {
      ret = env.makeType(et);
      if (!et->valueIndex.isEmpty()) {
        // if it has values, it's definitely been defined already
        env.error(stringc << "multiply defined enum `" << name << "'");
        return ret;      // ignore this defn
      }
    }
  }

  if (!et) {
    // declare the new enum
    et = new EnumType(name);
    ret = env.declareEnum(loc, et);
  }

  FAKELIST_FOREACH_NC(Enumerator, elts, iter) {
    iter->tcheck(env, et, ret);
  }

  this->etype = et;           // annotation
  return ret;
}


// BaseClass
// MemberList

// ---------------------- Member ----------------------
// cppstd 9.2 para 6:
//   "A member shall not be auto, extern, or register."
void checkMemberFlags(Env &env, DeclFlags flags)
{
  if (flags & (DF_AUTO | DF_EXTERN | DF_REGISTER)) {
    env.error("class members cannot be marked `auto', `extern', "
              "or `register'");
  }   
}

void MR_decl::tcheck(Env &env)
{
  env.setLoc(loc);

  if (!( d->dflags & DF_FRIEND )) {
    FAKELIST_FOREACH_NC(Declarator, d->decllist, iter) {
      env.checkForQualifiedMemberDeclarator(iter);
    }
  }

  if (env.secondPassTcheck) {
    // TS_classSpec is only thing of interest
    if (d->spec->isTS_classSpec()) {
      d->spec->asTS_classSpec()->tcheck(env, d->dflags);
    }
    return;
  }

  // the declaration knows to add its variables to
  // the curCompound
  d->tcheck(env, DC_MR_DECL);

  checkMemberFlags(env, d->dflags);
}

void MR_func::tcheck(Env &env)
{
  env.setLoc(loc);

  if (env.scope()->curCompound->keyword == CompoundType::K_UNION) {
    // TODO: is this even true?  
    // apparently not, as Mozilla has them; would like to find 
    // a definitive answer
    //env.error("unions cannot have member functions");
    //return;
  }

  if (!( f->dflags & DF_FRIEND )) {
    env.checkForQualifiedMemberDeclarator(f->nameAndParams);
  }

  // mark the function as inline, whether or not the
  // user explicitly did so
  f->dflags = (DeclFlags)(f->dflags | DF_INLINE);

  // we check the bodies in a second pass, after all the class
  // members have been added to the class, so that the potential
  // scope of all class members includes all function bodies
  // [cppstd sec. 3.3.6]
  //
  // the check-body suppression is now handled via a flag in 'env', so
  // this call site doesn't directly reflect that that is happening
  f->tcheck(env);

  checkMemberFlags(env, f->dflags);
}

void MR_access::tcheck(Env &env)
{
  if (env.secondPassTcheck) { return; }

  env.setLoc(loc);

  env.scope()->curAccess = k;
}

void MR_usingDecl::tcheck(Env &env)
{
  if (env.secondPassTcheck) { return; }

  env.setLoc(loc);
  decl->tcheck(env);
}

void MR_template::tcheck(Env &env)
{
  // maybe this will "just work"? crossing fingers..
  env.setLoc(loc);
  d->tcheck(env);
}


// -------------------- Enumerator --------------------
void Enumerator::tcheck(Env &env, EnumType *parentEnum, Type *parentType)
{
  var = env.makeVariable(loc, name, parentType, DF_ENUMERATOR);

  enumValue = parentEnum->nextValue;
  if (expr) {
    expr->tcheck(env, expr);

    // will either set 'enumValue', or print (add) an error message
    expr->constEval(env, enumValue);
  }

  parentEnum->addValue(name, enumValue, var);
  parentEnum->nextValue = enumValue + 1;

  // cppstd sec. 3.3.1:
  //   "The point of declaration for an enumerator is immediately after
  //   its enumerator-definition. [Example:
  //     const int x = 12;
  //     { enum { x = x }; }
  //   Here, the enumerator x is initialized with the value of the
  //   constant x, namely 12. ]"
           
  bool forceReplace = false;

  // (in/t0527.cc) will the name conflict with an implicit typedef?
  Variable *prior = env.unqualifiedLookup_one(name, LF_INNER_ONLY);
  if (prior && prior->isImplicitTypedef()) {
    TRACE("env", "replacing implicit typedef " << name << 
                 " with enumerator");
    forceReplace = true;
  }

  if (!env.addVariable(var, forceReplace)) {
    env.error(stringc
      << "enumerator " << name << " conflicts with an existing variable "
      << "or typedef by the same name");
  }
}


// ----------------- declareNewVariable ---------------   
// This block of helpers, especially 'declareNewVariable', is the
// heart of the type checker, and the most complicated.

// This function is called whenever a constructed type is passed to a
// lower-down IDeclarator which *cannot* accept member function types.
// (sm 7/10/03: I'm now not sure exactly what that means...)
//
// sm 8/10/04: the issue is that someone has to call 'doneParams', but
// that can't be done in one central location, so this does it unless
// it has already been done, and is called in several places;
// 'dt.funcSyntax' is used as a flag to tell when it's happened
void possiblyConsumeFunctionType(Env &env, Declarator::Tcheck &dt, 
                                 bool reportErrors = true)
{
  if (dt.funcSyntax) {
    if (dt.funcSyntax->cv != CV_NONE && reportErrors) {
      env.error("cannot have const/volatile on nonmember functions");
    }
    dt.funcSyntax = NULL;

    // close the parameter list
    env.doneParams(dt.type->asFunctionType());
  }
}


// given a 'dt.type' that is a function type, and a 'dt.funcSyntax'
// that's carrying information about the function declarator syntax,
// and 'inClass' the class that the function will be considered a
// member of, attach a 'this' parameter to the function type, and
// close its parameter list
void makeMemberFunctionType(Env &env, Declarator::Tcheck &dt,
                            NamedAtomicType *inClassNAT, SourceLoc loc)
{
  // make the implicit 'this' parameter
  CVFlags thisCV = dt.funcSyntax? dt.funcSyntax->cv : CV_NONE;
  Variable *receiver = env.receiverParameter(loc, inClassNAT, thisCV, dt.funcSyntax);

  // actually (in/k0031.cc), there is not necessarily a D_func, if a
  // typedef was used; in that case, the function cannot be 'const' or
  // 'volatile', and we need to make a copy of the function type so
  // that we can add the 'this' parameter
  FunctionType *ft = dt.type->asFunctionType();
  if (!dt.funcSyntax) {
    FunctionType *copyFt =
      env.tfac.makeSimilarFunctionType(SL_UNKNOWN, ft->retType, ft);

    // copy the parameters; it should be ok to share them (shallow copy)
    copyFt->params = ft->params;

    // use 'copyFt' from here on
    ft = copyFt;
  }

  // add the receiver to the function type
  ft->addReceiver(receiver);

  // close it
  dt.funcSyntax = NULL;
  env.doneParams(ft);
}


// Check some restrictions regarding the use of 'operator'; might
// add some errors to the environment, but otherwise doesn't
// change anything.  Parameters are same as declareNewVariable, plus
// 'scope', the scope into which the name will be inserted.
void checkOperatorOverload(Env &env, Declarator::Tcheck &dt,
                           SourceLoc loc, PQName const *name,
                           Scope *scope)
{
  if (!dt.type->isFunctionType()) {
    env.error(loc, "operators must be functions");
    return;
  }
  FunctionType *ft = dt.type->asFunctionType();

  // caller guarantees this will work
  OperatorName const *oname = name->getUnqualifiedNameC()->asPQ_operatorC()->o;
  char const *strname = oname->getOperatorName();

  if (scope->curCompound) {
    // All the operators mentioned in 13.5 must be non-static if they
    // are implemented by member functions.  (Actually, 13.5.7 does
    // not explicitly require non-static, but it's clearly intended.)
    //
    // That leaves only operators new and delete, which (12.5 para 1)
    // are always static *even if not explicitly declared so*.
    if (oname->isON_newDel()) {
      // actually, this is now done elsewhere (search for "12.5 para 1")
      //dt.dflags |= DF_STATIC;      // force it to be static
    }
    else if (dt.dflags & DF_STATIC) {
      env.error(loc, "operator member functions (other than new/delete) cannot be static");
    }
  }

  // describe the operator
  enum OperatorDesc {
    OD_NONE    = 0x00,
    NONMEMBER  = 0x01,      // can be a non-member function (anything can be a member function)
    ONEPARAM   = 0x02,      // can accept one parameter
    TWOPARAMS  = 0x04,      // can accept two parameters
    ANYPARAMS  = 0x08,      // can accept any number of parameters
    INCDEC     = 0x10,      // it's ++ or --
  };
  OperatorDesc desc = OD_NONE;

  ASTSWITCHC(OperatorName, oname) {
    ASTCASEC(ON_newDel, n)
      PRETEND_USED(n);
      // don't check anything.. I haven't done anything with these yet
      return;

    ASTNEXTC(ON_operator, o)
      static int/*OperatorDesc*/ const map[] = {
        // each group of similar operators is prefixed with a comment
        // that says which section of cppstd specifies the restrictions
        // that are enforced here

        // 13.5.1
        NONMEMBER | ONEPARAM,                       // OP_NOT
        NONMEMBER | ONEPARAM,                       // OP_BITNOT

        // 13.5.7
        NONMEMBER | ONEPARAM | TWOPARAMS | INCDEC,  // OP_PLUSPLUS
        NONMEMBER | ONEPARAM | TWOPARAMS | INCDEC,  // OP_MINUSMINUS

        // 13.5.1, 13.5.2
        NONMEMBER | ONEPARAM | TWOPARAMS,           // OP_PLUS
        NONMEMBER | ONEPARAM | TWOPARAMS,           // OP_MINUS
        NONMEMBER | ONEPARAM | TWOPARAMS,           // OP_STAR
        NONMEMBER | ONEPARAM | TWOPARAMS,           // OP_AMPERSAND

        // 13.5.2
        NONMEMBER | TWOPARAMS,                      // OP_DIV
        NONMEMBER | TWOPARAMS,                      // OP_MOD
        NONMEMBER | TWOPARAMS,                      // OP_LSHIFT
        NONMEMBER | TWOPARAMS,                      // OP_RSHIFT
        NONMEMBER | TWOPARAMS,                      // OP_BITXOR
        NONMEMBER | TWOPARAMS,                      // OP_BITOR

        // 13.5.3
        TWOPARAMS,                                  // OP_ASSIGN
        
        // 13.5.2 (these are handled as ordinary binary operators (13.5 para 9))
        NONMEMBER | TWOPARAMS,                      // OP_PLUSEQ
        NONMEMBER | TWOPARAMS,                      // OP_MINUSEQ
        NONMEMBER | TWOPARAMS,                      // OP_MULTEQ
        NONMEMBER | TWOPARAMS,                      // OP_DIVEQ
        NONMEMBER | TWOPARAMS,                      // OP_MODEQ
        NONMEMBER | TWOPARAMS,                      // OP_LSHIFTEQ
        NONMEMBER | TWOPARAMS,                      // OP_RSHIFTEQ
        NONMEMBER | TWOPARAMS,                      // OP_BITANDEQ
        NONMEMBER | TWOPARAMS,                      // OP_BITXOREQ
        NONMEMBER | TWOPARAMS,                      // OP_BITOREQ

        // 13.5.2
        NONMEMBER | TWOPARAMS,                      // OP_EQUAL
        NONMEMBER | TWOPARAMS,                      // OP_NOTEQUAL
        NONMEMBER | TWOPARAMS,                      // OP_LESS
        NONMEMBER | TWOPARAMS,                      // OP_GREATER
        NONMEMBER | TWOPARAMS,                      // OP_LESSEQ
        NONMEMBER | TWOPARAMS,                      // OP_GREATEREQ

        // 13.5.2
        NONMEMBER | TWOPARAMS,                      // OP_AND
        NONMEMBER | TWOPARAMS,                      // OP_OR

        // 13.5.6
        ONEPARAM,                                   // OP_ARROW

        // 13.5.2
        NONMEMBER | TWOPARAMS,                      // OP_ARROW_STAR

        // 13.5.5
        TWOPARAMS,                                  // OP_BRACKETS

        // 13.5.4
        ANYPARAMS,                                  // OP_PARENS

        // 13.5.2
        NONMEMBER | TWOPARAMS,                      // OP_COMMA
        
        OD_NONE,                                    // OP_QUESTION (not used)
        
        // I am guessing that <? and >? overload similar to OP_PLUS
        NONMEMBER | ONEPARAM | TWOPARAMS,           // OP_MINUMUM
        NONMEMBER | ONEPARAM | TWOPARAMS,           // OP_MAXIMUM
      };
      ASSERT_TABLESIZE(map, NUM_OVERLOADABLE_OPS);
      xassert(validCode(o->op));      
      
      // the table is declared int[] so that I can bitwise-OR
      // enumerated values without a cast; and overloading operator|
      // like I do elsewhere is nonportable b/c then an initializing
      // expression (which is supposed to be a literal) involves a
      // function call, at least naively...
      desc = (OperatorDesc)map[o->op];

      break;

    ASTNEXTC(ON_conversion, c)
      PRETEND_USED(c);
      desc = ONEPARAM;

    ASTENDCASECD
  }

  xassert(desc & (ONEPARAM | TWOPARAMS | ANYPARAMS));
            
  bool isMember = scope->curCompound != NULL;
  if (!isMember && !(desc & NONMEMBER)) {
    env.error(loc, stringc << strname << " must be a member function");
  }

  if (!(desc & ANYPARAMS)) {
    // count and check parameters
    int params = ft->params.count();     // includes implicit receiver
    bool okOneParam = desc & ONEPARAM;
    bool okTwoParams = desc & TWOPARAMS;

    if ((okOneParam && params==1) ||
        (okTwoParams && params==2)) {
      // ok
    }
    else {
      char const *howmany =
        okOneParam && okTwoParams? "one or two parameters" :
                      okTwoParams? "two parameters" :
                                   "one parameter" ;
      char const *extra =
        ft->isMethod()? " (including receiver object)" : "";
      env.error(loc, stringc << strname << " must have " << howmany << extra);
    }

    if ((desc & INCDEC) && (params==2)) {
      // second parameter must have type 'int'
      Type *t = ft->params.nth(1)->type;
      if (!t->isSimple(ST_INT) ||
          t->getCVFlags()!=CV_NONE) {
        env.error(loc, stringc
          << (isMember? "" : "second ")
          << "parameter of " << strname
          << " must have type `int', not `"
          << t->toString() << "', if it is present");
      }
    }

    // cannot have any default arguments
    SFOREACH_OBJLIST(Variable, ft->params, iter) {
      if (iter.data()->value != NULL) {
        env.error(loc, stringc << strname << " cannot have default arguments");
      }
    }
  }
}


bool forAnonymous_isUnion(Env &env, CompoundType::Keyword k)
{
  if (k == CompoundType::K_UNION) {
    return true;
  }

  if (env.lang.allowAnonymousStructs) {
    return true;
  }

  return false;
}


// This function is perhaps the most complicated in this entire
// module.  It has the responsibility of adding a variable called
// 'name' to the environment.  But to do this it has to implement the
// various rules for when declarations conflict, overloading,
// qualified name lookup, etc.
//
// Update: I've now broken some of this mechanism apart and implemented
// the pieces in Env, so it's perhaps a bit less complicated now.
//
// 8/11/04: I renamed it from D_name_tcheck, to reflect that it is no
// longer done at the bottom of the IDeclarator chain, but instead is
// done right after processing the IDeclarator,
// Declarator::mid_tcheck.
//
// Note that this function *cannot* return NULL.
static Variable *declareNewVariable(
  // environment in which to do general lookups
  Env &env,

  // contains various information about 'name', notably its type
  Declarator::Tcheck &dt,

  // true if we're a D_grouping is innermost to a D_pointer/D_reference
  bool inGrouping,

  // source location where 'name' appeared
  SourceLoc loc,

  // name being declared
  PQName *name)
{
  // this is used to refer to a pre-existing declaration of the same
  // name; I moved it up top so my error subroutines can use it
  Variable *prior = NULL;

  // the unqualified part of 'name', mapped if necessary for
  // constructor names
  StringRef unqualifiedName = name? name->getName() : NULL;

  // false until I somehow call doneParams() for function types
  bool consumedFunction = false;

  // scope in which to insert the name, and to look for pre-existing
  // declarations
  Scope *scope = env.acceptingScope(dt.dflags);
  
  // class that is befriending this entity
  CompoundType *befriending = NULL;

  goto realStart;

  // This code has a number of places where very different logic paths
  // lead to the same conclusion.  So, I'm going to put the code for
  // these conclusions up here (like mini-subroutines), and 'goto'
  // them when appropriate.  I put them at the top instead of the
  // bottom since g++ doesn't like me to jump forward over variable
  // declarations.  They aren't put into real subroutines because they
  // want to access many of this function's parameters and locals, and
  // it'd be a hassle to pass them all each time.  In any case, they
  // would all be tail calls, since once I 'goto' somewhere I don't
  // come back.

  // an error has been reported, but for error recovery purposes,
  // return something reasonable
  makeDummyVar:
  {
    if (!consumedFunction) {
      possiblyConsumeFunctionType(env, dt);
    }

    // the purpose of this is to allow the caller to have a workable
    // object, so we can continue making progress diagnosing errors
    // in the program; this won't be entered in the environment, even
    // though the 'name' is not NULL
    Variable *ret = env.makeVariable(loc, unqualifiedName, dt.type, dt.dflags);

    // set up the variable's 'scope' field as if it were properly
    // entered into the scope; this is for error recovery, in particular
    // for going on to check the bodies of methods
    scope->registerVariable(ret);

    return ret;
  }

realStart:
  if (!name) {
    // no name, nothing to enter into environment
    possiblyConsumeFunctionType(env, dt);
    return env.makeVariable(loc, NULL, dt.type, dt.dflags);
  }

  #if 0    // problematic since applies to too many things
  // C linkage?
  if (env.linkageIs_C()) {
    dt.dflags |= DF_EXTERN_C;
  }
  #endif // 0

  // friend?
  bool isFriend = (dt.dflags & DF_FRIEND);
  if (isFriend) {
    // TODO: somehow remember the access control implications
    // of the friend declaration

    // is the scope in which this declaration appears (that is,
    // skipping any template<> that might be associated directly 
    // with this declaration) itself a template?
    bool insideTemplate = env.enclosingKindScopeAbove(SK_TEMPLATE_PARAMS, scope);

    if (name->hasQualifiers() || insideTemplate) {
      // we're befriending something that either is already declared,
      // or will be declared before it is used; no need to contemplate
      // adding a declaration, so just make the required Variable
      // and be done with it
      //
      // TODO: can't befriend cv members, e.g. in/t0333.cc
      //
      // 2005-05-07: if we're in an uninst template (class), then
      // the friend declaration is ignored; it will be processed
      // when the template is instantiated (11.4, 14.5.3, in/t0470.cc)
      possiblyConsumeFunctionType(env, dt, false /*reportErrors*/);
      return env.makeVariable(loc, unqualifiedName, dt.type, dt.dflags);
    }
    else if (name->isPQ_template()) {
      // (e.g., in/t0474.cc) We are befriending a template.  Friends
      // and templates don't get along very well yet.  The most
      // immediate problem is that I need to look at the set of types
      // used in the friend declaration, and hypothesize a
      // corresponding set of template parameters that will be
      // associated with the friend, rather than being associated with
      // the class that is granting friendship.  At it is, with the
      // parameters associated with the class, I fail to realize that
      // a prior declaration is referring to the same thing.
      //
      // However, for right now, I think I can get away with ignoring
      // the friendship declaration altogether.
      goto makeDummyVar;
    }
    else {
      // 2005-08-15: record the befriending class so it can
      // participate in arg-dep lookup
      if (scope->curCompound) {
        befriending = scope->curCompound;
      }
      else {
        env.error("friend declaration must appear in class scope");
      }

      // the main effect of 'friend' in my implementation is to
      // declare the variable in the innermost non-class, non-
      // template scope (this isn't perfect; see cppstd 11.4)
      //
      // Unfortunately, both GCC and ICC seem to do name injection,
      // even though that is not what the standard specifies.  So,
      // making Elsa more standard-compliant on this issue would
      // create some static, and thus I do name injection too.
      scope = env.outerScope();

      // turn off the decl flag because it shouldn't end up
      // in the final Variable
      dt.dflags = dt.dflags & ~DF_FRIEND;
    }
  }

  // ambiguous grouped declarator in a paramter list?
  if (dt.hasFlag(DF_PARAMETER) && inGrouping) {
    // the name must *not* correspond to an existing type; this is
    // how I implement cppstd 8.2 para 7
    Variable *v = env.lookupPQ_one(name, LF_NONE);
    if (v && v->hasFlag(DF_TYPEDEF)) {
      TRACE("disamb", "discarding grouped param declarator of type name");
      env.error(stringc
        << "`" << *name << "' is the name of a type, but was used as "
        << "a grouped parameter declarator; ambiguity resolution should "
        << "pick a different interpretation, so if the end user ever "
        << "sees this message then there's a bug in my typechecker",
        EF_DISAMBIGUATES);
      goto makeDummyVar;
    }
  }

  // bhackett: disabling anonymous unions. we will find these by traversing
  // the anonymous structures when tchecking the E_fieldAcc for these fields
  // (there aren't other ways to access these fields since they are in a union)
  /*
  // member of an anonymous union?  (note that if the union had
  // declarators, then it would have been given a name by now)
  if (scope->curCompound &&
      scope->curCompound->name == NULL &&
      forAnonymous_isUnion(env, scope->curCompound->keyword)) {
    // we're declaring a field of an anonymous union, which actually
    // goes in the enclosing scope
    scope = env.enclosingScope();
  }
  */

  // constructor?
  bool isConstructor = dt.type->isFunctionType() &&
                       dt.type->asFunctionTypeC()->isConstructor();
  if (isConstructor) {
    // if I just use the class name as the name of the constructor,
    // then that will hide the class's name as a type, which messes
    // everything up.  so, I'll kludge together another name for
    // constructors (one which the C++ programmer can't type) and
    // just make sure I always look up constructors under that name
    unqualifiedName = env.constructorSpecialName;
  }

  // are we in a class member list?  we can't be in a member
  // list if the name is qualified (and if it's qualified then
  // a class scope has been pushed, so we'd be fooled); see
  // also Env::checkForQualifiedMemberDeclarator().
  CompoundType *enclosingClass =
    name->hasQualifiers()? NULL : scope->curCompound;

  // if we're in the scope of a class at all then we're DF_MEMBER
  if (scope->curCompound && !isFriend)
    dt.dflags |= DF_MEMBER;

  // if we're not in a class member list, and the type is not a
  // function type, and 'extern' is not specified, then this is
  // a definition
  if (!enclosingClass &&
      !dt.type->isFunctionType() &&
      !(dt.dflags & DF_EXTERN)) {
    dt.dflags |= DF_DEFINITION;
  }

  // has this variable already been declared?
  //Variable *prior = NULL;    // moved to the top

  if (name->hasQualifiers()) {
    // TODO: I think this is wrong, but I'm not sure how.  For one
    // thing, it's very similar to what happens below for unqualified
    // names; could those be unified?  Second, the thing above about
    // how class member declarations can be qualified, but I don't
    // allow it ...

    // the name has qualifiers, which means it *must* be declared
    // somewhere; now, Declarator::tcheck will have already pushed the
    // qualified scope, so we just look up the name in the now-current
    // environment, which will include that scope
    prior = scope->lookupVariable(unqualifiedName, env, LF_INNER_ONLY);
    if (!prior) {
      env.error(stringc
        << "undeclared identifier `" << *name << "'");
      goto makeDummyVar;
    }

    // ok, so we found a prior declaration; but if it's a member of
    // an overload set, then we need to pick the right one now for
    // several reasons:
    //   - the DF_DEFINITION flag is per-member, not per-set
    //   - below we'll be checking for type equality again
    if (prior->overload) {
      // only functions can be overloaded
      if (!dt.type->isFunctionType()) {
        env.error(dt.type, stringc
          << "the name `" << *name << "' is overloaded, but the type `"
          << dt.type->toString() << "' isn't even a function; it must "
          << "be a function and match one of the overloadings");
        goto makeDummyVar;
      }
      FunctionType *dtft = dt.type->asFunctionType();

      // 'dtft' is incomplete for the moment, because we don't know
      // yet whether it's supposed to be a static member or a
      // nonstatic member; this is determined by finding a function
      // whose signature (ignoring 'this' parameter, if any) matches
      int howMany = prior->overload->set.count();
      prior = env.findInOverloadSet(prior->overload, dtft, dt.funcSyntax->cv);
      if (!prior) {
        env.error(stringc
          << "the name `" << *name << "' is overloaded, but the type `"
          << dtft->toString_withCV(dt.funcSyntax->cv) 
          << "' doesn't match any of the "
          << howMany << " declared overloaded instances",
          EF_STRONG);
        goto makeDummyVar;
      }
    }

    if (prior->hasFlag(DF_MEMBER)) {
      // this intends to be the definition of a class member; make sure
      // the code doesn't try to define a nonstatic data member
      if (!prior->type->isFunctionType() &&
          !prior->hasFlag(DF_STATIC)) {
        env.error(stringc
          << "cannot define nonstatic data member `" << *name << "'");
        goto makeDummyVar;
      }
    }
  }
  else {
    // has this name already been declared in the innermost scope?
    prior = env.lookupVariableForDeclaration(scope, unqualifiedName, dt.type,
      dt.funcSyntax? dt.funcSyntax->cv : CV_NONE);
  }

  if (scope->curCompound &&
      !isFriend &&
      name->getUnqualifiedNameC()->isPQ_operator() &&
      name->getUnqualifiedNameC()->asPQ_operatorC()->o->isON_newDel()) {
    // 12.5 para 1: new/delete member functions are static even if
    // they are not explicitly declared so
    dt.dflags |= DF_STATIC;
  }

  // is this a nonstatic member function?
  //
  // TODO: This can't be right in the presence of overloaded functions,
  // since we're just testing the static-ness of the first element of
  // the overload set!
  if (dt.type->isFunctionType()) {
    if (scope->curCompound &&
        !isFriend &&
        !isConstructor &&               // ctors don't have a 'this' param
        !(dt.dflags & DF_STATIC) &&
        !(dt.dflags & DF_TYPEDEF) &&    // in/t0536.cc
        (!name->hasQualifiers() ||
         !prior->type->isFunctionType() ||
         prior->type->asFunctionTypeC()->isMethod())) {
      TRACE("memberFunc", "nonstatic member function: " << *name);

      // add the implicit 'this' parameter
      makeMemberFunctionType(env, dt, scope->curCompound, loc);
    }
    else {
      TRACE("memberFunc", "static or non-member function: " << *name);
      possiblyConsumeFunctionType(env, dt);
    }
  }
  consumedFunction = true;

  // check restrictions on operator overloading
  if (name->getUnqualifiedNameC()->isPQ_operator()) {
    checkOperatorOverload(env, dt, loc, name, scope);
  }

  // check for overloading; but if there are qualifiers, then we already
  // did overload resolution above
  OverloadSet *overloadSet =
    name->hasQualifiers() ? NULL /* already did it */ :
    env.getOverloadForDeclaration(prior, dt.type);

  // 8/11/04: Big block of template code obviated by
  // Declarator::mid_tcheck.

  // make a new variable; see implementation for details
  Variable *ret =
    env.createDeclaration(loc, unqualifiedName, dt.type, dt.dflags,
                          scope, enclosingClass, prior, overloadSet);

  if (befriending) {
    befriending->friends.prepend(ret);
  }
  
  return ret;
}


// -------------------- Declarator --------------------
Declarator *Declarator::tcheck(Env &env, Tcheck &dt)
{
  if (!ambiguity) {
    mid_tcheck(env, dt);
    return this;
  }

  // The reason for the "gcov-begin/end-ignore" below is that this
  // code is at the mercy of the parser when it comes to the order in
  // which ambiguous alternatives are presented.  So, I tell 'mygcov'
  // not to count coverage in the affected region.

  // As best as I can tell from the standard, cppstd sections 6.8 and
  // 8.2, we always prefer a Declarator interpretation which has no
  // initializer (if that's valid) to one that does.  I'm not
  // completely sure because, ironically, the English text there ("the
  // resolution is to consider any construct that could possibly be a
  // declaration a declaration") is ambiguous in my opinion.  See the
  // examples of ambiguous syntax in cc.gr, nonterminal
  // InitDeclarator.
  if (this->init == NULL &&
      ambiguity->init != NULL &&
      ambiguity->ambiguity == NULL) {                // gcov-begin-ignore
    // already in priority order
    return resolveAmbiguity(this, env, "Declarator", true /*priority*/, dt);
  }
  else if (this->init != NULL &&
           ambiguity->init == NULL &&
           ambiguity->ambiguity == NULL) {
    // reverse priority order; swap them
    return swap_then_resolveAmbiguity(this, env, "Declarator", true /*priority*/, dt);
  }                                                  // gcov-end-ignore
  else {
    // if both have an initialzer or both lack an initializer, then
    // we'll resolve without ambiguity; otherwise we'll probably fail
    // to resolve, which will be reported as such
    return resolveAmbiguity(this, env, "Declarator", false /*priority*/, dt);
  }
}


// array initializer case
//   static int y[] = {1, 2, 3};
// or in this case (a gnu extention):
// http://gcc.gnu.org/onlinedocs/gcc-3.3/gcc/Compound-Literals.html#Compound%20Literals
//   static int y[] = (int []) {1, 2, 3};
// which is equivalent to:
//   static int y[] = {1, 2, 3};
Type *Env::computeArraySizeFromCompoundInit(SourceLoc tgt_loc, Type *tgt_type,
                                            Type *src_type, Initializer *init)
{
  // If we start at a reference, we have to go down to the raw
  // ArrayType and then back up to a reference.
  bool tgt_type_isRef = tgt_type->isReferenceType();
  tgt_type = tgt_type->asRval();
  if (tgt_type->isArrayType() &&
      init->isIN_compound()) {
    ArrayType *at = tgt_type->asArrayType();
    IN_compound const *cpd = init->asIN_compoundC();
                   
    // count the initializers; this is done via the environment
    // so the designated-initializer extension can intercept
    int initLen = countInitializers(loc(), src_type, cpd);

    if (!at->hasSize()) {
      // replace the computed type with another that has
      // the size specified; the location isn't perfect, but
      // getting the right one is a bit of work
      tgt_type = tfac.setArraySize(tgt_loc, at, initLen);
    }
    else {
      // TODO: cppstd wants me to check that there aren't more
      // initializers than the array's specified size, but I
      // don't want to do that check since I might have an error
      // in my const-eval logic which could break a Mozilla parse
      // if my count is short
    }
  }
  return tgt_type_isRef ? makeReferenceType(tgt_type): tgt_type;
}

// provide a well-defined size for the array from the size of the
// initializer, such as in this case:
//   char sName[] = "SOAPPropertyBag";
Type *computeArraySizeFromLiteral(Env &env, Type *tgt_type, Initializer *&init)
{
  // If we start at a reference, we have to go down to the raw
  // ArrayType and then back up to a reference.
  bool tgt_type_isRef = tgt_type->isReferenceType();
  tgt_type = tgt_type->asRval();

  // also match against this weird case:
  // char sName[] = { "FUBARBAZ" };
  // computeArraySizeFromCompoundInit will have already made sName a char[1].
  bool handle_init = false;
  if (init->isIN_compound()) {
    if (tgt_type->isArrayType() &&
        tgt_type->asArrayType()->hasSize() &&
        tgt_type->reprSize() == 1) {
      init = init->asIN_compound()->inits.nth(0);
      handle_init = true;
    }
  }
  else if (tgt_type->isArrayType() &&
           !tgt_type->asArrayType()->hasSize()) {
    handle_init = true;
  }

  if (handle_init && init->isIN_expr() &&
      init->asIN_expr()->e->type->asRval()->isArrayType() &&
      init->asIN_expr()->e->type->asRval()->asArrayType()->hasSize()
      ) {
    tgt_type->asArrayType()->size =
      init->asIN_expr()->e->type->asRval()->asArrayType()->size;
    xassert(tgt_type->asArrayType()->hasSize());
  }

  return tgt_type_isRef ? env.makeReferenceType(tgt_type): tgt_type;
}

// true if the declarator corresponds to a local/global variable declaration
bool isVariableDC(DeclaratorContext dc)
{
  return dc==DC_TF_DECL ||    // global
         dc==DC_S_DECL ||     // local
         dc==DC_CN_DECL;      // local in a Condition
}

// determine if a complete type is required, and if so, check that it
// is; return false if a complete type is needed but 'type' is not
bool checkCompleteTypeRules(Env &env, DeclFlags dflags, DeclaratorContext context,
                            Type *type, Initializer *init)
{
  // TODO: According to 15.4 para 1, not only must the type in
  // DC_EXCEPTIONSPEC be complete (which this code enforces), but if
  // it is a pointer or reference type, the pointed-to thing must be
  // complete too!

  if (context == DC_D_FUNC) {
    // 8.3.5 para 6: ok to be incomplete unless this is a definition;
    // I'll just allow it (here) in all cases (t0048.cc)
    return true;
  }

  if (context == DC_ON_CONVERSION) {
    // similarly for the return type of a conversion operator (in/t0535.cc)
    return true;
  }

  if (context == DC_TA_TYPE) {
    // mere appearance of a type in an argument list is not enough to
    // require that it be complete; maybe the function definition will
    // need it, but that is detected later
    return true;
  }

  if (dflags & (DF_TYPEDEF | DF_EXTERN)) {
    // 7.1.3 does not say that the type named by a typedef must be
    // complete, so I will allow it to be incomplete (t0079.cc)
    //
    // I'm not sure where the exception for 'extern' is specified, but
    // it clearly exists.... (t0170.cc)
    return true;
  }        

  if (context == DC_MR_DECL &&
      (dflags & DF_STATIC)) {
    // static members don't have to be complete types
    return true;
  }

  if (context == DC_TF_DECL &&
      env.lang.uninitializedGlobalDataIsCommon &&
      !init) {
    // tentative global definition, type does not need to be complete;
    // c99 6.9.2p3 implies this is only allowed if 'static' is not
    // specified, but gcc does not enforce that so I won't either
    return true;
  }

  if (type->isArrayType()) {
    if (init) {
      // The array type might be incomplete now, but the initializer
      // will take care of it.  (If I instead moved this entire block
      // below where the init is tchecked, I think I would run into
      // problems when tchecking the initializer wants a ctor to exist.)
      // (t0077.cc)
      return true;
    }
                                       
    if (context == DC_MR_DECL &&
        !env.lang.strictArraySizeRequirements) {
      // Allow incomplete array types, so-called "open arrays".
      // Usually, such things only go at the *end* of a structure, but
      // we do not check that.
      return true;
    }

    #ifdef GNU_EXTENSION
    if (context == DC_E_COMPOUNDLIT) {
      // dsw: arrays in ASTTypeId's of compound literals are
      // allowed to not have a size and not have an initializer:
      // (gnu/g0014.cc)
      return true;
    }
    #endif // GNU_EXTENSION
  }

  // ok, we're not in an exceptional circumstance, so the type
  // must be complete; if we have an error, what will we say?
  char const *action = 0;
  switch (context) {                           
    default /*catch-all*/:     action = "create an object of"; break;
    case DC_EXCEPTIONSPEC:     action = "name in exception spec"; break;
    case DC_E_KEYWORDCAST:     // fallthru
    case DC_E_CAST:            action = "cast to"; break;
    case DC_E_SIZEOFTYPE:      action = "compute size of"; break;
  }

  // check it
  return env.ensureCompleteType(action, type);
}
 
// Is 't' an object type built in to the language, such that it
// could not possibly have a user-defined constructor?  It needs
// to not be a class of course, but also not a dependent type that
// could be instantiated with a class.
bool isPrimitiveObjectType(Type const *t)
{
  if (t->isCVAtomicType()) {
    AtomicType const *at = t->asCVAtomicTypeC()->atomic;
    return at->isSimpleType() || at->isEnumType();
  }

  return t->isPointerType() ||
         t->isReferenceType() ||
         t->isPointerToMemberType();
}

void Declarator::mid_tcheck(Env &env, Tcheck &dt)
{
  // true if we're immediately in a class body
  Scope *enclosingScope = env.scope();
  bool inClassBody = !!(enclosingScope->curCompound);
           
  // is this declarator in a templatizable context?  this prevents 
  // confusion when processing the template arguments themselves (which
  // contain declarators), among other things
  bool templatizableContext = 
    dt.context == DC_FUNCTION ||   // could be in MR_func or TD_func
    dt.context == DC_TD_DECL ||
    dt.context == DC_MR_DECL;

  LookupFlags lflags = LF_NONE;
  DeclFlags instFlags = DF_NONE;
  if (dt.context == DC_TF_EXPLICITINST) {
    // this tells the qualifier lookup code that there are no
    // template<> parameter lists to worry about
    lflags |= LF_EXPLICIT_INST;

    // grab the flags that were shuttled by Declarator::dflags
    // from TF_explicitInst::flags; this works in part because
    // only one declarator is allowed in an explicit instantiation
    DeclFlags const mask = DF_EXTERN | DF_STATIC | DF_INLINE;
    instFlags = dt.dflags & mask;
    dt.dflags &= ~mask;
  }

  PQName *name = decl->getDeclaratorId();
  if (!name && (dt.dflags & DF_TEMPL_PARAM)) {
    // give names to all template params, because we need to refer
    // to them in the self-name (in/t0493.cc)
    name = new PQ_name(this->getLoc(), env.getAnonName(getLoc(), "tparam"));
    this->setDeclaratorId(name);
  }

  // cppstd sec. 3.4.3 para 3:
  //    "In a declaration in which the declarator-id is a
  //    qualified-id, names used before the qualified-id
  //    being declared are looked up in the defining
  //    namespace scope; names following the qualified-id
  //    are looked up in the scope of the member's class
  //    or namespace."
  //
  // This is implemented by the following call.
  //
  // TODO: BUG: The names appearing in pointer-to-member constructors
  // must be looked up *before* pushing the declarator scopes.
  // (t0436.cc)
  ScopeSeq qualifierScopes;
  tcheckDeclaratorPQName(env, qualifierScopes, name, lflags);

  // the type constructed so far might refer to
  // DependentQTypes that now can (and must) be resolved more
  // precisely (t0290a.cc, t0438.cc, t0440.cc)
  if (name) {
    Type *t = env.resolveDQTs(name->loc, dt.type);
    if (t) {
      TRACE("dqt", "resolved " << dt.type->toString() << " to " << t->toString());
      dt.type = t;
    }
  }

  if (init) {
    dt.dflags |= DF_INITIALIZED;
  }

  // get the type from the IDeclarator
  decl->tcheck(env, dt);

  // this this a specialization of a global template function,
  // or a member template function?
  if (templatizableContext &&                      // e.g. toplevel
      enclosingScope->isTemplateParamScope() &&    // "template <...>" above
      !enclosingScope->parameterizedEntity) {      // that's mine, not my class' (need to wait until after name->tcheck to test this)
    if (dt.type->isFunctionType()) {
      // complete specialization?
      if (enclosingScope->templateParams.isEmpty()) {    // just "template <>"
        xassert(!dt.existingVar);
        dt.existingVar = env.makeExplicitFunctionSpecialization
                           (decl->loc, dt.dflags, name, dt.type->asFunctionType());
        if (dt.existingVar) {
          enclosingScope->setParameterizedEntity(dt.existingVar);
        }
      }

      else {
        // either a partial specialization, or a primary; since the
        // former doesn't exist for functions, there had better not
        // be any template arguments on the function name
        if (name->getUnqualifiedName()->isPQ_template()) {
          env.error("function template partial specialization is not allowed",
                    EF_STRONG);
        }
      }
    }
    else {
      // for class specializations, we should not get here, as the syntax
      //
      //   template <>
      //   class A<int> { ... }  /*declarator goes here*/  ;
      //
      // does not have (and cannot have) any declarators
      env.error("template class declaration must not have declarators", EF_STRONG);
    }
  }

  // explicit instantiation?
  if (dt.context == DC_TF_EXPLICITINST) {
    dt.existingVar = 
      env.explicitFunctionInstantiation(name, dt.type, instFlags);
  }

  // DF_FRIEND gets turned off by 'declareNewVariable' ...
  bool isFriend = !!(dt.dflags & DF_FRIEND);

  bool callerPassedInstV = false;
  if (!dt.existingVar) {
    // make a Variable, add it to the environment
    var = env.storeVar(
      declareNewVariable(env, dt, decl->hasInnerGrouping(), decl->loc, name));

    if (var &&
        var->name == env.string_main &&
        var->isGlobal()) {
      env.handleTypeOfMain(decl->loc, var, dt.type);
    }
  }
  else {
    // caller already gave me a Variable to use
    var = dt.existingVar;
    callerPassedInstV = true;

    // declareNewVariable is normally responsible for adding the receiver
    // param to 'dt.type', but since I skipped it, I have to do it
    // here too
    if (var->type->isFunctionType() &&
        var->type->asFunctionType()->isMethod()) {
      TRACE("memberFunc", "nonstatic member function: " << var->name);

      // add the implicit 'this' parameter
      makeMemberFunctionType(env, dt,
        var->type->asFunctionType()->getNATOfMember(), decl->loc);
    }
    else {
      TRACE("memberFunc", "static or non-member function: " << var->name);
      possiblyConsumeFunctionType(env, dt);
    }
  }
  xassert(var);

  type = dt.type;
  context = dt.context;

  if (decl->isD_bitfield()) {
    var->setBitfieldSize(decl->asD_bitfield()->numBits);
  }

  // declarators usually require complete types
  //
  // 2005-04-16: moved this down below the call to
  // 'declareNewVariable' to handle k0051.cc, where we need to match a
  // definition with a prior declaration to get a complete type
  if (!checkCompleteTypeRules(env, dt.dflags, context, var->type, init)) {
    // need to tell the calling context there is a problem
    type = dt.type = var->type = env.errorType();
  }

  // handle function template declarations ....
  TemplateInfo *templateInfo = NULL;
  if (callerPassedInstV) {
    // don't try to take it; dt.var probably already has it, etc.
  }
  else if (templatizableContext) {
    if (dt.type->isFunctionType()) {
      bool allowInherited = true;
      if (isFriend) {
        // (k0057.cc) we are processing the declaration of a
        // templatized friend; since the friend is not actually a
        // member of the current class, it should not be regarded as
        // parameterized by the current class's parameters (if any)
        allowInherited = false;
      }
      templateInfo = env.takeFTemplateInfo(allowInherited);
    }
    else {
      // non-templatizable entity
      //
      // TODO: I should allow static members of template classes
      // to be templatizable too
    }
  }
  else {
    // other contexts: don't try to take it, you're not a
    // templatizable declarator
  }

  if (templateInfo) {
    TRACE("template", "template func " << 
                      ((dt.dflags & DF_DEFINITION) ? "defn" : "decl")
                      << ": " << dt.type->toCString(var->fullyQualifiedName()));

    if (!var->templateInfo()) {
      // this is a new template decl; attach it to the Variable
      var->setTemplateInfo(templateInfo);

      // (what was I about to do here?)

    }
    else {
      // TODO: merge default arguments

      if (dt.dflags & DF_DEFINITION) {
        // save this templateInfo for use with the definition  
        //
        // TODO: this really should just be TemplateParams, not
        // a full TemplateInfo ...
        var->templateInfo()->definitionTemplateInfo = templateInfo;
      }
      else {
        // discard this templateInfo
        delete templateInfo;
      }
    }

    // no such thing as a function partial specialization, so this
    // is automatically the primary
    if (enclosingScope->isTemplateParamScope() &&
        !enclosingScope->parameterizedEntity) {
      enclosingScope->setParameterizedEntity(var);
    }

    // sm: I'm not sure what this is doing.  It used to only be done when
    // 'var' had no templateInfo to begin with.  Now I'm doing it always,
    // which might not be right.
    if (getDeclaratorId() &&
        getDeclaratorId()->isPQ_template()) {
      if (var->type->isFunctionType() &&
          (var->type->asFunctionType()->isConstructor() ||
           var->type->asFunctionType()->isDestructor())) {   // k0019.cc
        // in/t0461.cc: template args on the name are simply naming the
        // type that this function constructs, so should not be copied
      }
      else if (var->templateInfo()->isPrimary()) {           // k0019.cc error 1
        // need to avoid attaching the arguments in this case, because
        // that would create a malformed TemplateInfo object
        env.error(getLoc(), "template primary cannot have template args");
      }
      else {
        copyTemplateArgs(var->templateInfo()->arguments,
                         getDeclaratorId()->asPQ_templateC()->sargs);
      }
    }
  }
  
  else /* !templateInfo */ {
    TemplateInfo *ti = var->templateInfo();
    if (ti && ti->isInstantiation() &&               // var seems to be an instantiation
        enclosingScope->isTemplateParamScope() &&    // "template <...>" above
        enclosingScope->templateParams.isEmpty()) {  // just "template <>"
      // (in/t0475.cc) This is an explicit specialization of a member
      // of a class template.  The existing 'var->templateInfo' will
      // claim this is an (implicit) instantiation, but the explicit
      // specialization overrides that.
      ti->changeToExplicitSpec();
    }
  }

  // cppstd, sec. 3.3.1:
  //   "The point of declaration for a name is immediately after
  //   its complete declarator (clause 8) and before its initializer
  //   (if any), except as noted below."
  // (where "below" talks about enumerators, class members, and
  // class names)
  //
  // However, since the bottom of the recursion for IDeclarators
  // is always D_name, it's equivalent to add the name to the
  // environment then instead of here.

  // want only declarators corresp. to local/global variables
  // (it is disturbing that I have to check for so many things...)
  if (env.lang.isCplusplus &&
      !dt.hasFlag(DF_EXTERN) &&                 // not an extern decl
      !dt.hasFlag(DF_TYPEDEF) &&                // not a typedef
      isVariableDC(dt.context)) {               // local/global variable
    // 2005-08-05: I now question the wisdom of doing these
    // transformations, because if the type's constructor is entirely
    // compiler-supplied, then using an IN_ctor misleadingly suggests
    // that arbitrary computation could be happening...
    if (var->type->isCompoundType()) {            // class-valued
      if (!init) {
        // cppstd 8.5 paras 7,8,9: treat
        //   C c;
        // like
        //   C c();
        // except that the latter is not actually allowed since it would
        // be interpreted as a declaration of a function
        init = new IN_ctor(decl->loc, decl->loc, NULL /*args*/);
      }
      else if (init->isIN_expr()) {
        // treat
        //   C c = 5;
        // like
        //   C c(5);
        // except the latter isn't always syntactically allowed (e.g. CN_decl),
        // and isn't always equivalent [8.5p14]; was_IN_ctor will remember

        // take out the IN_expr
        IN_expr *inexpr = init->asIN_expr();
        Expression *e = inexpr->e;
        inexpr->e = NULL;
        delete inexpr;

        // put in an IN_ctor
        IN_ctor *inctor = new IN_ctor(decl->loc, decl->loc, makeExprList1(e));
        inctor->was_IN_expr = true;
        init = inctor;
      }
    }
    
    // for non-class types, normalize IN_ctor into IN_expr, as this
    // makes it clear that no function call is occurring, and is how
    // constant-value variables are recognized (in/t0512.cc)
    else if (init &&
             isPrimitiveObjectType(var->type) &&
             init->isIN_ctor()) {
      IN_ctor *inc = init->asIN_ctor();
      if (inc->args->count() != 1) {
        env.error(getLoc(), stringc
          << "expected constructor-style initializer of `"
          << var->type->toString() << "' to have 1 argument, not "
          << inc->args->count());
      }
      else {
        // substitute IN_expr
        init = new IN_expr(getLoc(), getLoc(), inc->args->first()->expr);
        
        // Above, I dispose of the replaced initializer, but that is
        // only valid if I am sure that no other AST node is pointing
        // at it, and I am not.  So, just leave 'inc' alone.  (The
        // code above may or may not be wrong, but since it has not
        // been observed to fail I won't mess with it.)
      }
    }
  }

  // tcheck the initializer, unless we're inside a class, in which
  // case wait for pass two
  //
  // 8/06/04: dsw: why wait until pass 2?  I need to change it to pass
  // 1 to get in/d0088.cc to work and all the other elsa and oink
  // tests also work
  //
  // sm: You're right; I had thought 3.3.6 said that member scopes
  // included *all* initializers, but it does not, so such scopes only
  // include *subsequent* initializers, hence pass 1 is the right time.
  //
  // 2005-02-17:  I think I Now I understand.  3.3.6 para 1 bullet 1
  // says that *default arguments* must be tchecked in pass 2, and
  // that may have been the original intent.  I am changing it so
  // default arguments are skipped here (checked by
  // DefaultArgumentChecker); *member initializers* will continue to
  // be tcheck'd in pass 1.  Testcase: in/t0369.cc.
  if (dt.context == DC_D_FUNC &&
      !env.checkFunctionBodies) {
    // skip it
  }
  else if (init) {
    // TODO: check the initializer for compatibility with
    // the declared type

    // TODO: check compatibility with dflags; e.g. we can't allow
    // an initializer for a global variable declared with 'extern'

    tcheck_init(env);
  }

  // pull the scope back out of the stack; if this is a
  // declarator attached to a function definition, then
  // Function::tcheck will re-extend it for analyzing
  // the function body
  env.retractScopeSeq(qualifierScopes);

  // If it is a function, is it virtual?
  if (inClassBody
      && var->type->isMethod()
      && !var->hasFlag(DF_VIRTUAL)) {
    FunctionType *varft = var->type->asFunctionType();
    CompoundType *myClass = env.scope()->curCompound;

    // search among base classes
    SObjList<BaseClassSubobj const> subobjs;
    myClass->getSubobjects(subobjs);
    SFOREACH_OBJLIST(BaseClassSubobj const, subobjs, iter) {
      CompoundType *base = iter.data()->ct;
      if (base == myClass) { continue; }

      // get all variables with this name
      LookupSet set;
      base->lookup(set, var->name, NULL /*env*/, LF_INNER_ONLY);

      // look for any virtual functions with matching signatures
      SFOREACH_OBJLIST(Variable, set, iter2) {
        Variable const *var2 = iter2.data();

        if (var2->hasFlag(DF_VIRTUAL) && var2->type->isFunctionType()) {
          FunctionType *var2ft = var2->type->asFunctionType();
          if (var2ft->equalOmittingReceiver(varft) &&
              var2ft->getReceiverCV() == varft->getReceiverCV()) {
            // make this one virtual too
            var->setFlag(DF_VIRTUAL);
            goto done_with_virtual_stuff;    // two-level break
          }
        }
      }
    }

    done_with_virtual_stuff:;
  }
}


// pulled out so it could be done in pass 1 or pass 2
void Declarator::tcheck_init(Env &env)
{
  xassert(init);

  init->tcheck(env, type);

  // TODO: check the initializer for compatibility with
  // the declared type

  // TODO: check compatibility with dflags; e.g. we can't allow
  // an initializer for a global variable declared with 'extern'

  // remember the initializing value, for const values
  if (init->isIN_expr()) {
    var->value = init->asIN_exprC()->e;
  }

  // use the initializer size to refine array types
  // array initializer case
  var->type = env.computeArraySizeFromCompoundInit(var->loc, var->type, type, init);
  // array compound literal initializer case
  var->type = computeArraySizeFromLiteral(env, var->type, init);

  // update 'type' if necessary
  //
  // (k0018.cc) check if 'var->type' is an array, rather than just
  // 'type', so we see the type after parameter type normalization
  if (var->type->asRval()->isArrayType()) {
    type->asRval()->asArrayType()->size = var->type->asRval()->asArrayType()->size;
  }
}


// ------------------ IDeclarator ------------------
void D_name::tcheck(Env &env, Declarator::Tcheck &dt)
{
  env.setLoc(loc);

  // 7/27/04: This has been disabled because Declarator::mid_tcheck
  // takes care of tchecking the name in advance.
  //if (name) {
  //  name->tcheck(env);
  //}

  // do *not* call 'possiblyConsumeFunctionType', since declareNewVariable
  // will do so if necessary, and in a different way
}


// cppstd, 8.3.2 para 4:
//   "There shall be no references to references, no arrays of
//    references, and no pointers to references."

void D_pointer::tcheck(Env &env, Declarator::Tcheck &dt)
{
  env.setLoc(loc);
  possiblyConsumeFunctionType(env, dt);

  if (dt.type->isReference()) {
    env.error("cannot create a pointer to a reference");
  }
  else {
    // apply the pointer type constructor
    if (!dt.type->isError()) {
      dt.type = env.tfac.syntaxPointerType(loc, cv, dt.type, this);
    }
  }

  // recurse
  base->tcheck(env, dt);
}

// almost identical to D_pointer ....
void D_reference::tcheck(Env &env, Declarator::Tcheck &dt)
{
  env.setLoc(loc);
  possiblyConsumeFunctionType(env, dt);

  if (dt.type->isReference()) {
    env.error("cannot create a reference to a reference");
  }
  else {
    // apply the reference type constructor
    if (!dt.type->isError()) {
      dt.type = env.tfac.syntaxReferenceType(loc, dt.type, this);
    }
  }

  // recurse
  base->tcheck(env, dt);
}


// this code adapted from (the old) tcheckFakeExprList; always passes NULL
// for the 'sizeExpr' argument to ASTTypeId::tcheck
FakeList<ASTTypeId> *tcheckFakeASTTypeIdList(
  FakeList<ASTTypeId> *list, Env &env, DeclFlags dflags, DeclaratorContext context)
{
  if (!list) {
    return list;
  }

  // context for checking (ok to share these across multiple ASTTypeIds)
  ASTTypeId::Tcheck tc(dflags, context);

  // check first ASTTypeId
  FakeList<ASTTypeId> *ret
    = FakeList<ASTTypeId>::makeList(list->first()->tcheck(env, tc));

  // check subsequent expressions, using a pointer that always
  // points to the node just before the one we're checking
  ASTTypeId *prev = ret->first();
  while (prev->next) {
    prev->next = prev->next->tcheck(env, tc);

    prev = prev->next;
  }

  return ret;
}

// implement cppstd 8.3.5 para 3:
//   "array of T" -> "pointer to T"
//   "function returning T" -> "pointer to function returning T"
// also, since f(int) and f(int const) are the same function (not
// overloadings), strip toplevel cv qualifiers
static Type *normalizeParameterType(Env &env, SourceLoc loc, Type *t)
{
  if (t->isArrayType()) {
    return env.makePtrType(t->asArrayType()->eltType);
  }
  if (t->isFunctionType()) {
    return env.makePtrType(t);
  }

  // 2005-05-27: I started to implement stripping of 'cv' from the
  // parameters, as the comment above suggests, but then realized that
  // would mean that even inside the definition, parameters' cv is
  // lost.  Therefore the new plan is to make EF_IGNORE_PARAM_CV
  // effectively always true, as no function *type* is ever supposed
  // to have cv on its parameters.

  return t;
}


void D_func::tcheck(Env &env, Declarator::Tcheck &dt)
{
  env.setLoc(loc);
  possiblyConsumeFunctionType(env, dt);

  FunctionFlags specialFunc = FF_NONE;

  // handle "fake" return type ST_CDTOR
  if (dt.type->isSimple(ST_CDTOR)) {
    if (env.lang.isCplusplus) {
      // get the name being declared
      D_name *dname;
      PQName *name;
      {
        // get the D_name one level down (skip D_groupings)
        IDeclarator *idecl = base;
        while (idecl->isD_grouping()) {
          idecl = idecl->asD_grouping()->base;
        }
        xassert(idecl->isD_name());    // grammar should ensure this
        dname = idecl->asD_name();

        // skip qualifiers
        name = dname->name->getUnqualifiedName();
      }

      // conversion operator
      if (name->isPQ_operator()) {
        if (name->asPQ_operator()->o->isON_conversion()) {
          ON_conversion *conv = name->asPQ_operator()->o->asON_conversion();

          // compute the named type; this becomes the return type
          ASTTypeId::Tcheck tc(DF_NONE, DC_ON_CONVERSION);
          conv->type = conv->type->tcheck(env, tc);
          dt.type = conv->type->getType();
          specialFunc = FF_CONVERSION;
        }
        else {
          env.diagnose3(env.lang.allowImplicitIntForOperators, name->loc,
                        stringc << "cannot declare `" << name->toString() 
                                << "' with no return type (MSVC bug accepts it)");
          dt.type = env.getSimpleType(ST_INT);     // recovery
        }
      }

      // constructor or destructor
      else {
        StringRef nameString = name->getName();
        CompoundType *inClass = env.acceptingScope()->curCompound;

        // destructor
        if (nameString[0] == '~') {
          if (!inClass) {
            env.error("destructors must be class members");
          }
          else if (!streq(nameString+1, inClass->name)) {
            env.error(stringc
              << "destructor name `" << nameString
              << "' must match the class name `" << inClass->name << "'");
          }

          // return type is 'void'
          dt.type = env.getSimpleType(ST_VOID);
          specialFunc = FF_DTOR;
        }

        // constructor
        else {
          if (!inClass) {
            if (!env.lang.allowImplicitInt &&
                env.lang.allowImplicitIntForMain &&
                nameString == env.str("main")) {
              // example: g0018.cc
              env.warning("obsolete use of implicit int in declaration of main()");

              // change type to 'int'
              dt.type = env.getSimpleType(ST_INT);
            }
            else {
              env.error("constructors must be class members (and implicit int is not supported)");
              
              // 2005-03-09: At one point I had the following:
              //
              //    return;    // otherwise would segfault below..
              //
              // but it appears there is no longer a risk of segfault,
              // and by removing the 'return' I will consistently
              // return a FunctionType from a D_func declarator, which
              // helps other parts of the code.
            }
          }
          else {
            if (nameString != inClass->name) {
              // I'm not sure if this can occur...
              env.error(stringc
                << "constructor name `" << nameString
                << "' must match the class name `" << inClass->name << "'");
            }

            // return type is same as class type
            dt.type = env.makeType(inClass);
            specialFunc = FF_CTOR;
          }
        }
      }
    }
    
    else {     // C
      if (env.lang.allowImplicitInt) {
        // surely this is not adequate, as implicit-int applies to
        // all declarations, not just those that appear in function
        // definitions... I think the rest of the implementation is
        // in Oink?
        dt.type = env.getSimpleType(ST_INT);
      }
      else {
        env.error("support for omitted return type is currently off");
      }
    }
  }

  // make a new scope for the parameter list
  Scope *paramScope = env.enterScope(SK_PARAMETER, "D_func parameter list scope");

  // typecheck the parameters; this disambiguates any ambiguous type-ids,
  // and adds them to the environment
  params = tcheckFakeASTTypeIdList(params, env, DF_PARAMETER, DC_D_FUNC);

  // build the function type; I do this after type checking the parameters
  // because it's convenient if 'syntaxFunctionType' can use the results
  // of checking them
  FunctionType *ft = env.tfac.syntaxFunctionType(loc, dt.type, this, env.tunit);
  ft->flags = specialFunc;
  #ifdef KANDR_EXTENSION
    if (kAndR_params) {
      ft->setFlag(FF_KANDR_DEFN);
    }
  #endif
  dt.funcSyntax = this;

  // add them, now that the list has been disambiguated
  int ct=0;
  FAKELIST_FOREACH_NC(ASTTypeId, params, iter) {
    ct++;
    Variable *v = iter->decl->var;

    if (v->type->isSimple(ST_VOID)) {
      if (ct == 1 &&
          !iter->next &&
          !v->name &&
          !iter->decl->init) {
        // special case: only parameter is "void" and it doesn't have a name:
        // same as empty param list
        break;
      }
      env.error("cannot have parameter of type `void', unless it is "
                "the only parameter, has no parameter name, and has "
                "no default value");
      continue;
    }

    if (v->type->isSimple(ST_ELLIPSIS)) {
      // no need for as careful checking as for ST_VOID, since the
      // grammar ensures it's last if it appears at all
      ft->flags |= FF_VARARGS;
      break;
    }

    v->type = normalizeParameterType(env, loc, v->type);

    // get the default argument, if any
    if (iter->decl->init) {
      Initializer *i = iter->decl->init;
      xassert(i->isIN_expr());    // ensured by grammar
    }

    // dsw: You didn't implement adding DF_PARAMETER to variables that
    // are parameters; This seems to be the best place to put it.
    v->setFlag(DF_PARAMETER);
    ft->addParam(v);
  }

  // dsw: in K&R C, an empty parameter list means that the number of
  // arguments is not specified
  if (env.lang.emptyParamsMeansNoInfo && params->isEmpty()) {
    ft->flags |= FF_NO_PARAM_INFO;
  }

  if (specialFunc == FF_CONVERSION) {
    if (ft->params.isNotEmpty() || ft->acceptsVarargs()) {
      env.error("conversion operator cannot accept arguments");
    }
  }

  // the verifier will type-check the pre/post at this point
  env.checkFuncAnnotations(ft, this);

  env.exitScope(paramScope);

  if (exnSpec) {
    ft->exnSpec = exnSpec->tcheck(env);
  }

  // call this after attaching the exception spec, if any
  //env.doneParams(ft);
  // update: doneParams() is done by 'possiblyConsumeFunctionType'
  // or 'declareNewVariable', depending on what declarator is next in
  // the chain

  // now that we've constructed this function type, pass it as
  // the 'base' on to the next-lower declarator
  dt.type = ft;

  base->tcheck(env, dt);
}


void D_array::tcheck(Env &env, Declarator::Tcheck &dt)
{
  env.setLoc(loc);
  possiblyConsumeFunctionType(env, dt);

  // check restrictions in cppstd 8.3.4 para 1
  if (dt.type->isReference()) {
    env.error("cannot create an array of references");
    return;
  }
  if (dt.type->isSimple(ST_VOID)) {
    env.error("cannot create an array of void");
    return;
  }
  if (dt.type->isFunctionType()) {
    env.error("cannot create an array of functions");
    return;
  }
  // TODO: check for abstract classes

  // cppstd 8.3.4 para 1:
  //   "cv-qualifier array of T" -> "array of cv-qualifier T"
  // hmmm.. I don't know what syntax would give rise to
  // the former, or at least my AST can't represent it.. oh well

  if (size) {
    // typecheck the 'size' expression
    size->tcheck(env, size);
  }

  ArrayType *at;

  if (dt.context == DC_E_NEW) {
    // we're in a new[] (E_new) type-id
    if (!size) {
      env.error("new[] must have an array size specified");
      at = env.makeArrayType(dt.type);    // error recovery
    }
    else {
      if (base->isD_name()) {
        // this is the final size expression, it need not be a
        // compile-time constant; this 'size' is not part of the type
        // of the objects being allocated, rather it is a dynamic
        // count of the number of objects to allocate
        dt.size_E_new = size;
        this->isNewSize = true;     // annotation

        // now just call into the D_name to finish off the type; dt.type
        // is left unchanged, because this D_array contributed nothing
        // to the *type* of the objects we're allocating
        base->tcheck(env, dt);
        return;
      }
      else {
        // this is an intermediate size, so it must be a compile-time
        // constant since it is part of a description of a C++ type
        int sz;
        if (!size->constEval(env, sz)) {
          // error has already been reported; this is for error recovery
          at = env.makeArrayType(dt.type);
        }
        else {
          // TODO: If 'sz' is dependent, then we need to construct some
          // kind of ArrayType whose size is an arbitrary expression.

          // construct the type
          at = env.makeArrayType(dt.type, sz);
        }
      }
    }
  }

  else {
    // we're not in an E_new, so add the size to the type if it's
    // specified; there are some contexts which require a type (like
    // definitions), but we'll report those errors elsewhere
    if (size) {
      // try to evaluate the size to a constant
      int sz = 1;
      ConstEval cenv(env.dependentVar);
      CValue val = size->constEval(cenv);
      TypeVariable *depType = NULL;

      if (val.isError()) {
        // size didn't evaluate to a constant
        sz = ArrayType::NO_SIZE;
        if ((dt.context == DC_S_DECL ||
             // dsw: if it is a struct declared local to a function,
             // then gcc in C mode allows it to have dynamic size
             (dt.context == DC_MR_DECL && env.enclosingKindScope(SK_FUNCTION)) ||
             // 2005-05-26: C99 functions can have arrays with dynamic
             // size; TODO: do a better job recording the semantics of
             // such declarations, for the benefit of analyses (in/c/dC0021.c)
             (dt.context == DC_D_FUNC && env.scope()->scopeKind == SK_PARAMETER) ||
             // 2005-05-31: (in/c/dC0031.c) dynamically-sized arrays in
             // sizeof and alignof
             #ifdef GNU_EXTENSION
               dt.context == DC_E_ALIGNOFTYPE ||
             #endif
             dt.context == DC_E_SIZEOFTYPE
            ) &&
            env.lang.allowDynamicallySizedArrays) {
          // allow it anyway
          sz = ArrayType::DYN_SIZE;
        }
        else {
          // report the error
          env.error(*(val.getWhy()));
        }
        delete val.getWhy();
      }
      else if (val.isDependent()) {
        sz = ArrayType::DEP_SIZE;

        // bhackett: match against the case we're interested in for doing eventual
        // template parameter inference, where the size is a plain type variable
        // (this seems to be the only case gcc handles). constEval does not keep
        // enough information around for this.

        if (E_variable *nsize = size->ifE_variable()) {
          if (PQ_name *nname = nsize->name->ifPQ_name())
            depType = new TypeVariable(nname->name);
        }

        // if (!depType)
        //   env.warning(loc, stringc << "unknown dependent array size");
      }
      else if (val.isIntegral()) {
        sz = val.getIntegralValue();

        // check restrictions on array size (c.f. cppstd 8.3.4 para 1)
        if (env.lang.strictArraySizeRequirements) {
          if (sz <= 0) {
            env.error(loc, stringc << "array size must be positive (it is " << sz << ")");
          }
        }
        else {
          if (sz < 0) {
            env.error(loc, stringc << "array size must be nonnegative (it is " << sz << ")");
          }
        }
      }
      else {
        env.error(loc, "array size must have integral type");
      }

      at = env.makeArrayType(dt.type, sz);
      at->depType = depType;
    }
    else {
      // no size
      at = env.makeArrayType(dt.type);
    }
  }

  // having added this D_array's contribution to the type, pass
  // that on to the next declarator
  dt.type = at;
  base->tcheck(env, dt);
}


void D_bitfield::tcheck(Env &env, Declarator::Tcheck &dt)
{
  env.setLoc(loc);
  possiblyConsumeFunctionType(env, dt);

  if (name) {
    // shouldn't be necessary, but won't hurt
    tcheckPQName(name, env, NULL, LF_DECLARATOR);
  }

  bits->tcheck(env, bits);

  // check that the expression is a compile-time constant
  int n;
  if (!bits->constEval(env, n)) {
    env.error("bitfield size must be a constant", EF_NONE);
  }
  else {
    // remember the size of the bit field
    this->numBits = n;
  }
  
  dt.dflags |= DF_BITFIELD;
}


void D_ptrToMember::tcheck(Env &env, Declarator::Tcheck &dt)
{
  env.setLoc(loc);                   
  
  // typecheck the nested name
  tcheckPQName(nestedName, env, NULL /*scope*/, LF_NONE);

  // enforce [cppstd 8.3.3 para 3]
  if (dt.type->isReference()) {
    env.error("you can't make a pointer-to-member refer to a reference type");
    return;

    // there used to be some recovery code here, but I decided it was
    // better to just bail entirely rather than tcheck into 'base' with
    // broken invariants
  }

  if (dt.type->isVoid()) {
    env.error("you can't make a pointer-to-member refer to `void'");
    return;
  }

  // find the compound to which it refers
  // (previously I used lookupPQCompound, but I believe that is wrong
  // because this is a lookup of a nested-name-specifier (8.3.3) and
  // such lookups are done in the variable space (3.4.3))
  Variable *ctVar = env.lookupPQ_one(nestedName, LF_ONLY_TYPES);
  if (!ctVar) {
    env.error(stringc
      << "cannot find type `" << nestedName->toString()
      << "' for pointer-to-member");
    return;
  }

  // allow the pointer to point to a member of a class (CompoundType),
  // *or* a TypeVariable (for templates)
  NamedAtomicType *nat = ctVar->type->ifNamedAtomicType();
  if (!nat) {
    env.error(stringc
      << "in ptr-to-member, `" << nestedName->toString()
      << "' does not refer to a class nor is a type variable");
    return;
  }

  if (dt.type->isFunctionType()) {
    // add the 'this' parameter to the function type, so the
    // full type becomes "pointer to *member* function"
    makeMemberFunctionType(env, dt, nat, loc);
  }

  // build the ptr-to-member type constructor
  dt.type = env.tfac.syntaxPointerToMemberType(loc, nat, cv, dt.type, this);

  // recurse
  base->tcheck(env, dt);
}


void D_grouping::tcheck(Env &env, Declarator::Tcheck &dt)
{
  env.setLoc(loc);

  // don't call 'possiblyConsumeFunctionType', since the
  // D_grouping is supposed to be transparent

  base->tcheck(env, dt);
}


bool IDeclarator::hasInnerGrouping() const
{
  bool ret = false;

  IDeclarator const *p = this;
  while (p) {
    switch (p->kind()) {
      // turn off the flag because innermost so far is now
      // a pointer type constructor
      case D_POINTER:
        ret = false;
        break;
      case D_REFERENCE:
        ret = false;
        break;
      case D_PTRTOMEMBER:
        ret = false;
        break;

      // turn on the flag b/c innermost is now grouping
      case D_GROUPING:
        ret = true;
        break;
              
      // silence warning..
      default:
        break;
    }

    p = p->getBaseC();
  }

  return ret;
}


// ------------------- ExceptionSpec --------------------
FunctionType::ExnSpec *ExceptionSpec::tcheck(Env &env)
{
  FunctionType::ExnSpec *ret = new FunctionType::ExnSpec;

  // typecheck the list, disambiguating it
  types = tcheckFakeASTTypeIdList(types, env, DF_NONE, DC_EXCEPTIONSPEC);

  // add the types to the exception specification
  FAKELIST_FOREACH_NC(ASTTypeId, types, iter) {
    ret->types.append(iter->getType());
  }

  return ret;
}


// ------------------ OperatorName ----------------
char const *ON_newDel::getOperatorName() const
{
  // changed the names so that they can be printed out with these
  // names and it will be the correct syntax; it means the identifier
  // has a space in it, which isn't exactly ideal, but the alternative
  // (ad-hoc decoding) isn't much better
  return (isNew && isArray)? "operator new[]" :
         (isNew && !isArray)? "operator new" :
         (!isNew && isArray)? "operator delete[]" :
                              "operator delete";
}

char const *ON_operator::getOperatorName() const
{
  xassert(validCode(op));
  return operatorFunctionNames[op];
}

char const *ON_conversion::getOperatorName() const
{
  // this is the sketchy one..
  // update: but it seems to be fitting into the design just fine
  return "conversion-operator";
}


void OperatorName::tcheck(Env &env)
{
  if (isON_conversion()) {
    ON_conversion *conv = asON_conversion();
    
    // check the "return" type
    ASTTypeId::Tcheck tc(DF_NONE, DC_ON_CONVERSION);
    conv->type->tcheck(env, tc);
  }
  else {
    // nothing to do for other kinds of OperatorName
  }
}


// ---------------------- Statement ---------------------
Statement *Statement::tcheck(Env &env)
{
  env.setLoc(loc);

  int dummy;
  if (!ambiguity) {
    // easy case
    mid_tcheck(env, dummy);
    return this;
  }

  Statement *ret = resolveImplIntAmbig(env, this);
  if (ret) {
    return ret->tcheck(env);
  }

  // the only ambiguity for Statements I know if is S_decl vs. S_expr,
  // and this one is always resolved in favor of S_decl if the S_decl
  // is a valid interpretation [cppstd, sec. 6.8]
  if (this->isS_decl() && ambiguity->isS_expr() &&
      ambiguity->ambiguity == NULL) {                  // gcov-begin-ignore
    // S_decl is first, run resolver with priority enabled
    return resolveAmbiguity(this, env, "Statement", true /*priority*/, dummy);
  }
  else if (this->isS_expr() && ambiguity->isS_decl() &&
           ambiguity->ambiguity == NULL) {
    // swap the expr and decl
    return swap_then_resolveAmbiguity(this, env, "Statement", true /*priority*/, dummy);
  }                                                    // gcov-end-ignore
  
  // unknown ambiguity situation
  xfailure("unknown statement ambiguity");
  return this;        // silence warning
}


// dsw: it is too slow to have emacs reload cc.ast.gen.h just to display
// the body of this method when I'm looking around in the stack in gdb
void Statement::mid_tcheck(Env &env, int &)
{
  itcheck(env);
}


void S_skip::itcheck(Env &env)
{}


void S_label::itcheck(Env &env)
{
  // this is a prototypical instance of typechecking a
  // potentially-ambiguous subtree; we have to change the
  // pointer to whatever is returned by the tcheck call
  s = s->tcheck(env);
  
  // TODO: check that the label is not a duplicate
}


void S_case::itcheck(Env &env)
{                    
  expr->tcheck(env, expr);
  s = s->tcheck(env);

  // TODO: check that the expression is of a type that makes
  // sense for a switch statement, and that this isn't a
  // duplicate case

  // UPDATE: dsw: whatever you do here, do it in
  // gnu.cc:S_rangeCase::itcheck() as well
                           
  // compute case label value
  expr->constEval(env, labelVal);
}


void S_default::itcheck(Env &env)
{
  s = s->tcheck(env);
  
  // TODO: check that there is only one 'default' case
}


void S_expr::itcheck(Env &env)
{
  expr->tcheck(env);
}


void S_compound::itcheck(Env &env)
{ 
  Scope *scope = env.enterScope(SK_FUNCTION, "compound statement");

  FOREACH_ASTLIST_NC(Statement, stmts, iter) {
    // have to potentially change the list nodes themselves
    iter.setDataLink( iter.data()->tcheck(env) );
  }

  env.exitScope(scope);
}


// Given a (reference to) a pointer to a statement, make it into an
// S_compound if it isn't already, so that it will be treated as having
// its own local scope (cppstd 6.4 para 1, 6.5 para 2).  Note that we
// don't need this for try-blocks, because their substatements are 
// *required* to be compound statements already.
void implicitLocalScope(Statement *&stmt)
{
  if (!stmt->isS_compound()) {
    Statement *orig = stmt;
    stmt = new S_compound(orig->loc, orig->end_loc, new ASTList<Statement>(orig));
  }
}


void S_if::itcheck(Env &env)
{
  // if 'cond' declares a variable, its scope is the
  // body of the "if"
  Scope *scope = env.enterScope(SK_FUNCTION, "condition in an 'if' statement");

  // 6.4 para 1
  implicitLocalScope(thenBranch);
  implicitLocalScope(elseBranch);

  cond = cond->tcheck(env);
  thenBranch = thenBranch->tcheck(env);
  elseBranch = elseBranch->tcheck(env);

  env.exitScope(scope);
}


void S_switch::itcheck(Env &env)
{
  Scope *scope = env.enterScope(SK_FUNCTION, "condition in a 'switch' statement");

  // 6.4 para 1
  implicitLocalScope(branches);

  cond = cond->tcheck(env);
  branches = branches->tcheck(env);

  env.exitScope(scope);
}


void S_while::itcheck(Env &env)
{
  Scope *scope = env.enterScope(SK_FUNCTION, "condition in a 'while' statement");

  // 6.5 para 2
  implicitLocalScope(body);

  cond = cond->tcheck(env);
  body = body->tcheck(env);

  env.exitScope(scope);
}


void S_doWhile::itcheck(Env &env)
{
  // 6.5 para 2
  implicitLocalScope(body);

  body = body->tcheck(env);
  expr->tcheck(env);

  // TODO: verify that 'expr' makes sense in a boolean context
}


void S_for::itcheck(Env &env)
{
  Scope *scope = env.enterScope(SK_FUNCTION, "condition in a 'for' statement");

  // 6.5 para 2
  implicitLocalScope(body);

  init = init->tcheck(env);
  cond = cond->tcheck(env);
  after->tcheck(env);
  body = body->tcheck(env);

  env.exitScope(scope);
}


void S_break::itcheck(Env &env)
{
  // TODO: verify we're in the context of a 'switch'
}


void S_continue::itcheck(Env &env)
{
  // TODO: verify we're in the context of a 'switch'
}


void S_return::itcheck(Env &env)
{
  if (expr) {
    expr->tcheck(env);
    
    // TODO: verify that 'expr' is compatible with the current
    // function's declared return type
  }

  else {
    // TODO: check that the function is declared to return 'void'
  }
}


void S_goto::itcheck(Env &env)
{
  // TODO: verify the target is an existing label
}


void S_decl::itcheck(Env &env)
{
  decl->tcheck(env, DC_S_DECL);
}


void S_try::itcheck(Env &env)
{
  body->tcheck(env);
  
  FAKELIST_FOREACH_NC(Handler, handlers, iter) {
    iter->tcheck(env);
  }
  
  // TODO: verify the handlers make sense in sequence:
  //   - nothing follows a "..." specifier
  //   - no duplicates
  //   - a supertype shouldn't be caught after a subtype
}


void S_asm::itcheck(Env &env)
{
  Expression *rep = text;
  text->tcheck(env, rep);
}


void S_namespaceDecl::itcheck(Env &env)
{
  decl->tcheck(env);
}


// ------------------- Condition --------------------
Condition *Condition::tcheck(Env &env)
{
  int dummy;
  if (!ambiguity) {
    // easy case
    mid_tcheck(env, dummy);
    return this;
  }

  // generic resolution: whatever tchecks is selected
  return resolveAmbiguity(this, env, "Condition", false /*priority*/, dummy);
}

void CN_expr::itcheck(Env &env)
{
  expr->tcheck(env);

  // TODO: verify 'expr' makes sense in a boolean or switch context
}


void CN_decl::itcheck(Env &env)
{
  ASTTypeId::Tcheck tc(DF_NONE, DC_CN_DECL);
  typeId = typeId->tcheck(env, tc);
  
  // TODO: verify the type of the variable declared makes sense
  // in a boolean or switch context
}


// ------------------- Handler ----------------------
void Handler::tcheck(Env &env)
{
  Scope *scope = env.enterScope(SK_FUNCTION, "exception handler");

  // originally, I only did this for the non-isEllpsis() case, to
  // avoid creating a type with ST_ELLIPSIS in it.. but cc_qual
  // finds it convenient, so now we tcheck 'typeId' always
  //
  // dsw: DF_PARAMETER: we think of the handler as an anonymous inline
  // function that is simultaneously defined and called in the same
  // place
  ASTTypeId::Tcheck tc(DF_PARAMETER, DC_HANDLER);
  typeId = typeId->tcheck(env, tc);

  body->tcheck(env);

  env.exitScope(scope);
}


// ------------------- Expression tcheck -----------------------
Type *makeLvalType(TypeFactory &tfac, Type *underlying)
{
  if (underlying->isLval()) {
    // this happens for example if a variable is declared to
    // a reference type
    return underlying;
  }
  else if (underlying->isFunctionType()) {
    // don't make references to functions
    return underlying;

    // at one point I added a similar prohibition against
    // references to arrays, but that was wrong, e.g.:
    //   int (&a)[];
  }
  else {
    return tfac.makeReferenceType(underlying);
  }
}

Type *makeLvalType(Env &env, Type *underlying)
{
  return makeLvalType(env.tfac, underlying);
}


// make the type of a field 'field', but is being accessed in an
// object whose reference is qualified with 'cv'
Type *makeFieldLvalType(Env &env, Variable *var, CVFlags cv)
{      
  Type *t = var->type;
  if (t->isReferenceType() || t->isFunctionType()) {
    return t;
  }

  if (var->hasFlag(DF_MUTABLE)) {
    cv = cv & ~CV_CONST;    // mutable defeats const (in/t0529.cc) [7.1.1p9]
  }

  t = env.tfac.applyCVToType(env.loc(), cv, t, NULL /*syntax*/);
  return env.tfac.makeReferenceType(t);
}


// There are several things going on with the replacement pointer.
//
// First, since Expressions can be ambiguous, when we select among
// ambiguous Expressions, the replacement is used to tell which one
// to use.  The caller then stores that instead of the original
// pointer.
//
// Second, to support elaboration of implicit function calls, an
// Expression node can decide to replace itself with a different
// kind of node (e.g. overloaded operators), or to insert another
// Expression above it (e.g. user-defined conversion functions).
//
// Finally, the obvious design would call for 'replacement' being
// a return value from 'tcheck', but I found that it was too easy
// to forget to update the original pointer.  So I changed the
// interface so that the original pointer cannot be forgotten, since
// a reference to it is now a parameter.


void Expression::tcheck(Env &env, Expression *&replacement)
{
  // the replacement point should always start out in agreement with
  // the receiver object of the 'tcheck' call; consequently,
  // Expressions can leave it as-is and no replacement will happen
  xassert(replacement == this);

  if (!ambiguity) {
    mid_tcheck(env, replacement);
    return;
  }

  // There is one very common ambiguity, between E_funCall and
  // E_constructor, and this ambiguity happens to frequently stack
  // upon itself, leading to worst-case exponential tcheck time.
  // Since it can be resolved easily in most cases, I special-case the
  // resolution.
  if ( ( (this->isE_funCall() &&
          this->ambiguity->isE_constructor() ) ||
         (this->isE_constructor() &&
          this->ambiguity->isE_funCall()) ) &&
      this->ambiguity->ambiguity == NULL) {
    E_funCall *call;
    E_constructor *ctor;
    if (this->isE_funCall()) {
      call = this->asE_funCall();             // gcov-begin-ignore
      ctor = ambiguity->asE_constructor();
    }
    else {
      ctor = this->asE_constructor();
      call = ambiguity->asE_funCall();
    }                                         // gcov-end-ignore

    // The code that follows is essentially resolveAmbiguity(),
    // specialized to two particular kinds of nodes, but only
    // tchecking the first part of each node to disambiguate.
    IFDEBUG( SourceLoc loc = env.loc(); )
    TRACE("disamb", toString(loc) << ": ambiguous: E_funCall vs. E_constructor");

    // grab errors
    ErrorList existing;
    existing.takeMessages(env.errors);

    // common case: function call
    TRACE("disamb", toString(loc) << ": considering E_funCall");
    LookupSet candidates;
    call->inner1_itcheck(env, candidates);
    if (noDisambErrors(env.errors)) {
      // ok, finish up; it's safe to assume that the E_constructor
      // interpretation would fail if we tried it
      TRACE("disamb", toString(loc) << ": selected E_funCall");
      env.errors.prependMessages(existing);
      call->type = call->inner2_itcheck(env, candidates);
      call->ambiguity = NULL;
      replacement = call;
      return;
    }

    // grab the errors from trying E_funCall
    ErrorList funCallErrors;
    funCallErrors.takeMessages(env.errors);

    // try the E_constructor interpretation
    TRACE("disamb", toString(loc) << ": considering E_constructor");
    ctor->inner1_itcheck(env);
    if (noDisambErrors(env.errors)) {
      // ok, finish up
      TRACE("disamb", toString(loc) << ": selected E_constructor");
      env.errors.prependMessages(existing);
      
      // a little tricky because E_constructor::inner2_itcheck is
      // allowed to yield a replacement AST node
      replacement = ctor;
      Type *t = ctor->inner2_itcheck(env, replacement);

      replacement->type = t;
      replacement->ambiguity = NULL;
      return;
    }

    // both failed.. just leave the errors from the function call
    // interpretation since that's the more likely intent
    env.errors.deleteAll();
    env.errors.takeMessages(existing);
    env.errors.takeMessages(funCallErrors);

    // 10/20/04: Need to give a type anyway.
    this->type = env.errorType();

    // finish up
    replacement = this;     // redundant but harmless
    return;
  }

  // some other ambiguity, use the generic mechanism; the return value
  // is ignored, because the selected alternative will be stored in
  // 'replacement'
  resolveAmbiguity(this, env, "Expression", false /*priority*/, replacement);
}


void Expression::mid_tcheck(Env &env, Expression *&replacement)
{
  // 2005-03-10: There used to be code here that would re-use an
  // already-computed type.  That code had been disabled for a long
  // time because it did not work; for example, the type of an
  // expression can depend on the context in which it appears.  So I
  // have now removed the code altogether, leaving only this note as a
  // reminder that that approach (along with several variations) was
  // tried and it failed.

  // during ambiguity resolution, 'replacement' is set to whatever
  // the original (first in the ambiguity list) Expression pointer
  // was; reset it to 'this', as that will be our "replacement"
  // unless the Expression wants to do something else
  replacement = this;

  // check it, and store the result
  Type *t = itcheck_x(env, replacement);

  // elaborate the AST by storing the computed type, *unless*
  // we're only disambiguating (because in that case many of
  // the types will be ST_ERROR anyway)
  //if (!env.onlyDisambiguating()) {
  //  type = t;
  //}
  //
  // update: made it unconditional again because after tcheck()
  // the callers expect to be able to dig in and find the type;
  // I guess I'll at some point have to write a visitor to
  // clear the computed types if I want to actually check the
  // template bodies after arguments are presented

  // dsw: putting the cloneType here means I can remove *many* of them
  // elsewhere, namely wherever an itcheck_x() returns.  This causes a
  // bit of garbage, since some of the types returned are partially
  // from somewhere else and partially made right there, such as
  // "return makeLvalType(t)" where "t" is an already existing type.
  // The only way I can think of to optimize that is to turn it in to
  // "return makeLvalType(env.tfac.cloneType(t))" and get rid of the
  // clone here; but that would be error prone and labor-intensive, so
  // I don't do it.
  replacement->type = t;
}


Type *E_boolLit::itcheck_x(Env &env, Expression *&replacement)
{
  // cppstd 2.13.5 para 1
  return env.getSimpleType(ST_BOOL);
}


// return true if type 'id' can represent value 'i'
bool canRepresent(SimpleTypeId id, unsigned long i)
{
  // I arbitrarily choose to make this determination according to the
  // representations available under the compiler that compiles Elsa,
  // since that's convenient and likely to correspond with what
  // happens when the source code in question is "really" compiled.

  switch (id) {
    default: xfailure("bad type id");

    case ST_INT:                 return i <= INT_MAX;
    case ST_UNSIGNED_INT:        return i <= UINT_MAX;
    case ST_LONG_INT:            return i <= LONG_MAX;

    case ST_UNSIGNED_LONG_INT:
    case ST_LONG_LONG:
    case ST_UNSIGNED_LONG_LONG:
      // I don't want to force the host compiler to have 'long long',
      // so I'm just going to claim that every value is representable
      // by these three types.  Also, given that I passed 'i' in as
      // 'unsigned long', it's pretty much a given that it will be
      // representable.
      return true;
  }
}

Type *E_intLit::itcheck_x(Env &env, Expression *&replacement)
{
  // cppstd 2.13.1 para 2

  char const *p = text;

  // what radix? (and advance 'p' past it)
  int radix = 10;
  if (*p == '0') {
    p++;
    if (*p == 'x' || *p == 'X') {
      radix = 16;
      p++;
    }
    else {
      radix = 8;
    }
  }

  // what value? (tacit assumption: host compiler's 'unsigned long'
  // is big enough to make these distinctions)
  i = strtoul(p, NULL /*endp*/, radix);

  // what suffix?
  while (isdigit(*p)) {
    p++;
  }
  bool hasU = false;
  int hasL = 0;
  if (*p == 'u' || *p == 'U') {
    hasU = true;
    p++;
  }
  if (*p == 'l' || *p == 'L') {
    hasL = 1;
    p++;
    if (*p == 'l' || *p == 'L') {
      hasL = 2;
      p++;
    }
  }
  if (*p == 'u' || *p == 'U') {
    hasU = true;
  }

  // The radix and suffix determine a sequence of types, and we choose
  // the smallest from the sequence that can represent the given value.

  // There are three nominal sequences, one containing unsigned types,
  // one with only signed types, and one with both.  In the tables
  // below, I will represent a sequence by pointing into one or the
  // other nominal sequence; the pointed-to element is the first
  // element in the effective sequence.  Sequences terminate with
  // ST_VOID.
  static SimpleTypeId const signedSeq[] = {
    ST_INT,                 // 0
    ST_LONG_INT,            // 1
    ST_LONG_LONG,           // 2
    ST_VOID
  };
  static SimpleTypeId const unsignedSeq[] = {
    ST_UNSIGNED_INT,        // 0
    ST_UNSIGNED_LONG_INT,   // 1
    ST_UNSIGNED_LONG_LONG,  // 2
    ST_VOID
  };
  static SimpleTypeId const mixedSeq[] = {
    ST_INT,                 // 0
    ST_UNSIGNED_INT,        // 1
    ST_LONG_INT,            // 2
    ST_UNSIGNED_LONG_INT,   // 3
    ST_LONG_LONG,           // 4
    ST_UNSIGNED_LONG_LONG,  // 5
    ST_VOID
  };

  // The following table layout is inspired by the table in C99
  // 6.4.4.1 para 5.

  // C99: (hasU + 2*hasL) x isNotDecimal -> typeSequence
  static SimpleTypeId const * const c99Map[6][2] = {
      // radix:  decimal              hex/oct
    // suffix:
    /* none */ { signedSeq+0,         mixedSeq+0 },
    /* U */    { unsignedSeq+0,       unsignedSeq+0 },
    /* L */    { signedSeq+1,         mixedSeq+2 },
    /* UL */   { unsignedSeq+1,       unsignedSeq+1 },
    /* LL */   { signedSeq+2,         mixedSeq+4 },
    /* ULL */  { unsignedSeq+2,       unsignedSeq+2 }
  };

  // The difference is in C++, the radix is only relevant when there
  // is no suffix.  Also, cppstd doesn't specify anything for 'long
  // long' (since that type does not exist in that language), so I'm
  // extrapolating its rules to that case.  Entries in the cppMap
  // that differ from c99Map are marked with "/*d*/".

  // C++: (hasU + 2*hasL) x isNotDecimal -> typeSequence
  static SimpleTypeId const * const cppMap[6][2] = {
      // radix:  decimal              hex/oct
    // suffix:
    /* none */ { signedSeq+0,         mixedSeq+0 },
    /* U */    { unsignedSeq+0,       unsignedSeq+0 },
    /* L */    { mixedSeq+2/*d*/,     mixedSeq+2 },
    /* UL */   { unsignedSeq+1,       unsignedSeq+1 },
    /* LL */   { mixedSeq+4/*d*/,     mixedSeq+4 },
    /* ULL */  { unsignedSeq+2,       unsignedSeq+2 }
  };

  // compute the sequence to use
  SimpleTypeId const *seq =
    env.lang.isCplusplus? cppMap[hasU + 2*hasL][radix!=10] :
                          c99Map[hasU + 2*hasL][radix!=10] ;

  // At this point, we pick the type that is the first type in 'seq'
  // that can represent the value.
  SimpleTypeId id = *seq;
  while (*(seq+1) != ST_VOID &&
         !canRepresent(id, i)) {
    seq++;
    id = *seq;
  }

  return env.getSimpleType(id);
}


Type *E_floatLit::itcheck_x(Env &env, Expression *&replacement)
{
  d = strtod(text, NULL /*endp*/);

  // what is the final character?
  char final = text[strlen(text)-1];
  if (final == 'f' || final == 'F') {
    return env.getSimpleType(ST_FLOAT);
  }
  if (final == 'l' || final == 'L') {
    return env.getSimpleType(ST_LONG_DOUBLE);
  }

  return env.getSimpleType(ST_DOUBLE);
}


Type *E_stringLit::itcheck_x(Env &env, Expression *&replacement)
{
  // cppstd 2.13.4 para 1

  // wide character?
  SimpleTypeId id = text[0]=='L'? ST_WCHAR_T : ST_CHAR;

  // TODO: this is wrong because I'm not properly tracking the string
  // size if it has escape sequences
  int len = 0;
  E_stringLit *p = this;
  while (p) {
    len += strlen(p->text) - 2;   // don't include surrounding quotes
    if (p->text[0]=='L') len--;   // don't count 'L' if present
    p = p->continuation;
  }

  CVFlags stringLitCharCVFlags = CV_NONE;
  if (env.lang.stringLitCharsAreConst) {
    stringLitCharCVFlags = CV_CONST;
  }
  Type *charConst = env.getSimpleType(id, stringLitCharCVFlags);
  Type *arrayType = env.makeArrayType(charConst, len+1);    // +1 for implicit final NUL

  // C++ 5.1p2, C99 6.5.1p4: string literals are lvalues (in/k0036.cc)
  Type *ret = makeLvalType(env, arrayType);
  
  // apply the same type to the continuations, for visitors' benefit
  for (p = continuation; p; p = p->continuation) {
    p->type = ret;
  }
  
  return ret;
}


void quotedUnescape(ArrayStack<char> &dest, char const *src,
                    char delim, bool allowNewlines)
{
  // strip quotes or ticks
  decodeEscapes(dest, substring(src+1, strlen(src)-2),
                delim, allowNewlines);
}

Type *E_charLit::itcheck_x(Env &env, Expression *&replacement)
{
  // cppstd 2.13.2 paras 1 and 2

  SimpleTypeId id = ST_CHAR;
  
  if (!env.lang.isCplusplus) {
    // nominal type of character literals in C is int, not char
    id = ST_INT;
  }

  char const *srcText = text;
  if (*srcText == 'L') {
    id = ST_WCHAR_T;
    srcText++;
  }

  ArrayStack<char> temp;
  quotedUnescape(temp, srcText, '\'', false /*allowNewlines*/);
  if (temp.length() == 0) {
    return env.error("character literal with no characters");
  }
  else if (temp.length() > 1) {
    // below I only store the first byte
    //
    // technically, this is ok, since multicharacter literal values
    // are implementation-defined; but Elsa is not so much its own
    // implementation as an approximation of some nominal "real"
    // compiler, which will no doubt do something smarter, so Elsa
    // should too
    env.warning("multicharacter literals not properly implemented");
    if (id == ST_CHAR) {
      // multicharacter non-wide character literal has type int
      id = ST_INT;
    }
  }

  // 2005-08-12: The first cast to 'unsigned char' will make sure that
  // negative chars (which come from things like '\xFF') get stored as
  // small positive ints in [128,255].  This is far from perfect, but
  // will do for now.
  c = (unsigned int)(unsigned char)temp[0];

  if (!env.lang.isCplusplus && id == ST_WCHAR_T) {
    // in C, 'wchar_t' is not built-in, it is defined; so we
    // have to look it up
    Variable *v = env.globalScope()->lookupVariable(env.str("wchar_t"), env);
    if (!v) {
      return env.error("you must #include <stddef.h> before using wchar_t");
    }
    else {
      return v->type;
    }
  }

  return env.getSimpleType(id);
}


Type *E_this::itcheck_x(Env &env, Expression *&replacement)
{
  // we should be in a method with a receiver parameter
  receiver = env.lookupVariable(env.receiverName);
  if (!receiver) {
    if (env.annotating) {
      return env.errorType();
    }
    else {
      return env.error("can only use 'this' in a nonstatic method");
    }
  }

  // compute type: *pointer* to the thing 'receiverVar' is
  // a *reference* to
  return env.makePointerType(CV_NONE, receiver->type->asRval());
}


E_fieldAcc *wrapWithImplicitThis(Env &env, Variable *var, PQName *name)
{
  // make *this
  E_this *ths = new E_this;
  Expression *thisRef = new E_deref(ths);
  thisRef->tcheck(env, thisRef);

  // sm: this assertion can fail if the method we are in right now
  // is static; the error has been reported, so just proceed
  //xassert(ths->receiver);

  CVFlags atTypeCV = CV_NONE;
  if (!ths->type->isError()) {
    atTypeCV = ths->type->getAtType()->getCVFlags();
  }

  // no need to tcheck as the variable has already been looked up
  E_fieldAcc *efieldAcc = new E_fieldAcc(thisRef, name);
  efieldAcc->field = var;

  // E_fieldAcc::itcheck_fieldAcc() does something a little more
  // complicated, but we don't need that since the situation is
  // more constrained here
  efieldAcc->type = makeFieldLvalType(env, var, atTypeCV);

  return efieldAcc;
}


Type *E_variable::itcheck_x(Env &env, Expression *&replacement)
{
  return itcheck_var(env, replacement, LF_NONE);
}

Type *E_variable::itcheck_var(Env &env, Expression *&replacement, LookupFlags flags)
{
  LookupSet dummy;
  return itcheck_var_set(env, replacement, flags, dummy);
}

Type *E_variable::itcheck_var_set(Env &env, Expression *&replacement,
                                  LookupFlags flags, LookupSet &candidates)
{
  tcheckPQName(name, env, NULL /*scope*/, LF_NONE);

  // re-use dependent?
  Variable *v = maybeReuseNondependent(env, name->loc, flags, nondependentVar);
  if (v) {
    var = v;
    
    // 2005-02-20: 'add' instead of 'adds', because when we remember a
    // non-dependent lookup, we do *not* want to re-do overload
    // resolution
    candidates.add(v);
  }
  else {
    // do lookup normally
    env.lookupPQ(candidates, name, flags);
    
    // gcc-2 hack
    if (candidates.isEmpty() &&
        env.lang.gcc2StdEqualsGlobalHacks &&
        isTwoPartName(env, name, "std", "getline")) {
      // try looking it up in global scope
      env.lookupPQ(candidates, name->getUnqualifiedName(), flags);
    }

    // compatibility with prior logic flow
    if (candidates.isNotEmpty()) {
      v = candidates.first();
    }

    if (v && v->hasFlag(DF_TYPEDEF)) {
      return env.error(name->loc, stringc
        << "`" << *name << "' used as a variable, but it's actually a type",
        EF_DISAMBIGUATES);
    }

    // 2005-02-18: cppstd 14.2 para 2: if template arguments are
    // supplied, then the name must look up to a template name
    if (v != env.dependentVar && 
        name->getUnqualifiedName()->isPQ_template()) {
      if (!v || !v->namesTemplateFunction()) {
        // would disambiguate use of '<' as less-than
        env.error(name->loc, stringc
          << "explicit template arguments were provided after `"
          << name->toString_noTemplArgs()
          << "', but that is not the name of a template function",
          EF_DISAMBIGUATES);
      }
    }

    if (!v) {
      // dsw: In K and R C it seems to be legal to call a function
      // variable that has never been declareed.  At this point we
      // notice this fact and if we are in K and R C we insert a
      // variable with signature "int ()(...)" which is what I recall as
      // the correct signature for such an implicit variable.
      if (env.lang.allowImplicitFunctionDecls && 
          (flags & LF_FUNCTION_NAME) &&
          name->isPQ_name()) {
        if (env.lang.allowImplicitFunctionDecls == B3_WARN) {
          env.warning(name->loc, stringc << "implicit declaration of `" << *name << "'");
        }

        v = env.makeImplicitDeclFuncVar(name->asPQ_name()->name);
      }
      else {
        if (flags & LF_SUPPRESS_NONEXIST) {
          // return a special type and do not insert an error message;
          // this is like a pending error that the caller should
          // resolve, either by making it a real error or (by using
          // argument dependent lookup) fix; ST_NOTFOUND should never
          // appear in the output of type checking
          return env.getSimpleType(ST_NOTFOUND);
        }

        // check to see if this is an access through some anonymous
        // structs or unions in this class.
        CompoundType *compound_type = env.enclosingClassScope();
        ArrayStack<Variable*> anon_fields;
        if (compound_type != NULL &&
            findAnonymousField(env, compound_type, name, anon_fields)) {

          // make a 'this->__anon_struct' for the outermost structure.
          Variable *anon = anon_fields.pop();
          PQName *anon_name = new PQ_name(anon->loc, anon->name);
          E_fieldAcc *obj = wrapWithImplicitThis(env, anon, anon_name);

          while (!anon_fields.isEmpty()) {
            Variable *field = anon_fields.pop();

            // get a new field access to the anonymous structure field.
            PQName *newField = new PQ_name(field->loc, field->name);
            obj = new E_fieldAcc(obj, newField);

            // fill in type and var for the field access. don't tcheck.
            obj->field = field;
            obj->type = makeFieldLvalType(env, field, CV_NONE);
          }

          replacement = obj;
          return obj->type;
        }

        if (env.annotating) {
          return env.errorType();
        }
        else {
          // 10/23/02: I've now changed this to non-disambiguating,
          // prompted by the need to allow template bodies to call
          // undeclared functions in a "dependent" context [cppstd 14.6
          // para 8].  See the note in TS_name::itcheck.
          return env.error(name->loc,
                           stringc << "there is no variable called `"
                                   << *name << "'",
                           EF_NONE);
        }
      }
    }
    xassert(v);

    // TODO: access control check

    var = env.storeVarIfNotOvl(v);

    // should I remember this non-dependent lookup?
    maybeNondependent(env, name->loc, nondependentVar, var);
  }

  if (var->isTemplateParam()) {
    // this variable is actually a bound meta-variable (template
    // argument), so it is *not* to be regarded as a reference
    // (14.1 para 6)

    // bhackett: if it was bound to a concrete value (an integer say)
    // we need to substitute that integer for the type.
    if (var->value) {
      replacement = var->value;
      replacement->tcheck(env, replacement);
    }

    return var->type;
  }

  // 2005-05-28: enumerators are not lvalues
  if (var->hasFlag(DF_ENUMERATOR)) {
    return var->type;
  }

  // elaborate 'this->'
  if (!(flags & LF_NO_IMPL_THIS) &&
      var->isMember() &&
      !var->isStatic()) {
    replacement = wrapWithImplicitThis(env, var, name);
    return replacement->type;
  }

  // return a reference because this is an lvalue
  return makeLvalType(env, var->type);
}

// ------------- BEGIN: outerResolveOverload ------------------


// set an ArgumentInfo according to an expression; this can only be
// used when the argument cannot be an overloaded function name
// (tcheckArgExprList handles the case where it can)
void getArgumentInfo(Env &env, ArgumentInfo &ai, Expression *e)
{
  ai.special = e->getSpecial(env.lang);
  ai.type = e->type;
}


// Given a Variable that might denote an overloaded set of functions,
// and the syntax of the arguments that are to be passed to the
// function ultimately chosen, pick one of the functions using
// overload resolution; return NULL if overload resolution fails for
// any reason. 'loc' is the location of the call site, for error
// reporting purposes.  (The arguments have already been tcheck'd.)
//
// This function mediates between the type checker, which knows about
// syntax and context, and the overload module's 'resolveOverload',
// which knows about neither.  In essence, it's everything that is
// common to overload resolution needed in various AST locations
// that isn't already covered by 'resolveOverload' itself.
//
// Note that it is up to the caller to do AST rewriting as necessary
// to reflect the chosen function.  Rationale: the caller is in a
// better position to know what things need to be rewritten, since it
// is fully aware of the syntactic context.
//
// The contract w.r.t. errors is: the caller must provide a non-NULL
// 'var', and if I return NULL, I will also add an error message, so
// the caller does not have to do so.
static Variable *outerResolveOverload(Env &env,
                                      PQName * /*nullable*/ finalName,
                                      SourceLoc loc, Variable *var,
                                      ArgumentInfoArray &argInfo)
{
  // if no overload set, nothing to resolve
  if (!var->overload) {
    return var;
  }

  return outerResolveOverload_explicitSet(env, finalName, loc, var->name,
                                          argInfo, var->overload->set);
}

static Variable *outerResolveOverload_explicitSet(
  Env &env,
  PQName * /*nullable*/ finalName,
  SourceLoc loc,
  StringRef varName,
  ArgumentInfoArray &argInfo,
  SObjList<Variable> &candidates)
{
  // special case: does 'finalName' directly name a particular
  // conversion operator?  e.g. in/t0226.cc
  if (finalName &&
      finalName->isPQ_operator() &&
      finalName->asPQ_operator()->o->isON_conversion()) {
    ON_conversion *conv = finalName->asPQ_operator()->o->asON_conversion();
    Type *namedType = conv->type->getType();

    // find the operator in the overload set
    SFOREACH_OBJLIST_NC(Variable, candidates, iter) {
      Type *iterRet = iter.data()->type->asFunctionType()->retType;
      if (iterRet->equals(namedType)) {
        return iter.data();
      }
    }

    env.error(stringc << "cannot find conversion operator yielding `"
                      << namedType->toString() << "'");
    return NULL;
  }

  OVERLOADINDTRACE(::toString(loc)
        << ": overloaded(" << candidates.count()
        << ") call to " << varName);      // if I make this fully qualified, d0053.cc fails...

  // 2005-02-23: There used to be code here that would bail on
  // overload resolution if any of the arguments was dependent.
  // However, that caused a problem (e.g. in/t0386.cc) because if the
  // receiver object is implicit, it does not matter if it is
  // dependent, but we cannot tell from here whether it was implicit.
  // Therefore I have moved the obligation of skipping overload
  // resolution to the caller, who *can* tell.

  // resolve overloading
  bool wasAmbig;     // ignored, since error will be reported
  return resolveOverload(env, loc, &env.errors,
                         OF_METHODS,    // TODO: always assume OF_METHODS in 'resolveOverload'
                         candidates, finalName, argInfo, wasAmbig);
}


// version of 'outerResolveOverload' for constructors; 'type' is the
// type of the object being constructed
static Variable *outerResolveOverload_ctor
  (Env &env, SourceLoc loc, Type *type, ArgumentInfoArray &argInfo)
{
  // skip overload resolution if any dependent args (in/t0412.cc)
  for (int i=0; i<argInfo.size(); i++) {
    Type *t = argInfo[i].type;
    if (t && t->containsGeneralizedDependent()) {
      return NULL;
    }
  }

  Variable *ret = NULL;
  // dsw: FIX: should I be generating error messages if I get a weird
  // type here, or if I get a weird var below?
  //
  // sm: at one point this code said 'asRval' but I think that is wrong
  // since we should not be treating the construction of a reference
  // the same as the construction of an object
  if (type->isCompoundType()) {
    env.ensureCompleteType("construct", type);
    CompoundType *ct = type->asCompoundType();
    Variable *ctor = ct->getNamedField(env.constructorSpecialName, env, LF_INNER_ONLY);

    // bhackett: disable for dealing with parse/tcheck errors.
    // xassert(ctor);
    if (!ctor)
      return NULL;

    Variable *chosen = outerResolveOverload(env,
                                            NULL, // finalName; none for a ctor
                                            loc,
                                            ctor,
                                            argInfo);
    if (chosen) {
      ret = chosen;
    } else {
      ret = ctor;
    }
  }
  // dsw: Note var can be NULL here for ctors for built-in types like
  // int; see t0080.cc
  return ret;
}
// ------------- END: outerResolveOverload ------------------



// There are a few variants of Expression that can return a lookup
// set, which is needed in some contexts.  This function dispatches
// appropriately from a context that can accept a set, depending on
// whether 'expr' can return one.  The existence of this function
// avoids the need to expand the parameter list of Expression::tcheck
// everywhere.  I am reserving the suffix "_set" for this family
// of functions.
void tcheckExpression_set(Env &env, Expression *&expr,
                          LookupFlags flags, LookupSet &set)
{
  Expression *origExpr = expr;

  Type *t;
  ASTSWITCH(Expression, expr) {
    ASTCASE(E_variable, evar)
      t = evar->itcheck_var_set(env, expr, flags, set);

    ASTNEXT(E_fieldAcc, eacc)
      t = eacc->itcheck_fieldAcc_set(env, /*no expr*/ flags, set);

    ASTNEXT(E_addrOf, ea)
      t = ea->itcheck_addrOf_set(env, expr, flags, set);

    ASTNEXT(E_grouping, eg)
      t = eg->itcheck_grouping_set(env, expr, flags, set);

    ASTNEXT(E_arrow, ea)
      t = ea->itcheck_arrow_set(env, expr, flags, set);

    ASTDEFAULT
      // 'expr' is not a variant that knows what to do with 'set',
      // so tcheck it normally; implicitly, 'expr->type' gets
      // set appropriately
      expr->tcheck(env, expr);
      return;

    ASTENDCASE
  }

  // the above assumed that the *original* was unambiguous, as it
  // totally ignored the ambiguity link; check that now
  xassert(origExpr->ambiguity == NULL);

  // must explicitly set 'expr->type' since we did not call
  // into Expression::tcheck
  expr->type = t;
}


// This function typechecks an argument list at a function call
// (E_funCall) or similar (E_constructor, etc.).  It fills in an
// ArgumentInfo array for possible use in overload resolution.  One
// complication is the need to deal with the possibility that an
// argument names an overloaded function, in which case we have to
// pass all the possibilities on to overload resolution.
FakeList<ArgExpression> *tcheckArgExprList(FakeList<ArgExpression> *list, Env &env,
                                           ArgumentInfoArray &argInfo,
                                           Type *receiverType /*= NULL*/)
{
  // always begin with the receiver, even if it is only a placeholder
  argInfo[0].special = SE_NONE;
  argInfo[0].type = receiverType? makeLvalType(env, receiverType) : NULL;

  // work through list, with an extra level of indirection so I can
  // modify the list links
  ArgExpression *first = list->first();
  ArgExpression **cur = &first;
  int i = 1;
  for (; *cur; cur = &((*cur)->next), i++) {
    argInfo.ensureIndexDoubler(i);
    ArgumentInfo &info = argInfo[i];

    *cur = (*cur)->tcheck(env, info);
  }

  // Initially, 'argInfo' had a size that was set by the caller, but
  // it does not always know the right size since the expression list
  // can be ambiguous (e.g., in/t0467.cc).  So, this code takes the
  // initial size as essentially a hint, but ensures when the expr
  // list is fully disambiguated, the size is set properly.
  argInfo.setSize(i);

  return FakeList<ArgExpression>::makeList(first);
}

ArgExpression *ArgExpression::tcheck(Env &env, ArgumentInfo &info)
{
  if (!ambiguity) {
    mid_tcheck(env, info);
    return this;
  }

  return resolveAmbiguity(this, env, "ArgExpression", false /*priority*/, info);
}
                      
// function or pointer to function
static bool isFunctionTypeOr(Type *t)
{
  if (t->isFunctionType()) {
    return true;
  }
  if (t->isPointerType() && t->getAtType()->isFunctionType()) {
    return true;
  }
  
  // could also be a pointer to a member function
  if (t->isPointerToMemberType() && t->getAtType()->isFunctionType()) {
    return true;
  }

  return false;
}

void tcheckArgumentExpression(Env &env, Expression *&expr, ArgumentInfo &info)
{
  // if the expression is an E_variable, possibly with an E_addrOf,
  // then we could do address-of overloaded function resolution,
  // so get a lookup set if possible
  LookupSet set;
  tcheckExpression_set(env, expr/*INOUT*/, LF_NONE /*?? LF_TEMPL_PRIMARY*/, set);

  if (set.isNotEmpty() &&
      isFunctionTypeOr(expr->type) &&
      (set.count() >= 2 || set.first()->isTemplate(false /*inh*/))) {
    info.special = SE_NONE;
    info.overloadSet = set;
  }
  else {
    info.special = expr->getSpecial(env.lang);
    info.type = expr->type;
  }
}

void ArgExpression::mid_tcheck(Env &env, ArgumentInfo &info)
{
  tcheckArgumentExpression(env, expr/*INOUT*/, info);
}


// This function is called *after* the arguments have been type
// checked and overload resolution performed (if necessary).  It must
// compare the actual arguments to the parameters.  It also must
// finish the job started above of resolving address-of overloaded
// function names, by comparing to the parameter.
//
// One bad aspect of the current design is the need to pass both 'args'
// and 'argInfo'.  Only by having both pieces of information can I do
// resolution of overloaded address-of.  I'd like to consolidate that
// at some point...
//
// Note that 'args' *never* includes the receeiver object, whereas
// 'argInfo' *always* includes the type of the recevier object (or
// NULL) as its first element.
//
// It returns the # of default args used.
int compareArgsToParams(Env &env, FunctionType *ft, FakeList<ArgExpression> *args,
                        ArgumentInfoArray &argInfo)
{
  int defaultArgsUsed = 0;

  if (!env.doCompareArgsToParams ||
      (ft->flags & FF_NO_PARAM_INFO)) {
    return defaultArgsUsed;
  }

  SObjListIterNC<Variable> paramIter(ft->params);
  int paramIndex = 1;
  FakeList<ArgExpression> *argIter = args;

  // for now, skip receiver object
  //
  // TODO (elaboration, admission): consider the receiver object as well
  if (ft->isMethod()) {
    paramIter.adv();
  }

  // iterate over both lists
  for (; !paramIter.isDone() && !argIter->isEmpty();
       paramIter.adv(), paramIndex++, argIter = argIter->butFirst()) {
    Variable *param = paramIter.data();
    ArgExpression *arg = argIter->first();

    // check correspondence between 'args' and 'argInfo'
    xassert(!argInfo[paramIndex].type ||
            arg->getType() == argInfo[paramIndex].type);

    // is the argument the name of an overloaded function? [cppstd 13.4]
    env.possiblySetOverloadedFunctionVar(arg->expr, param->type,
                                         argInfo[paramIndex].overloadSet);

    if (!param->type->isGeneralizedDependent()) {
      // try to convert the argument to the parameter
      ImplicitConversion ic = getImplicitConversion(env,
        arg->getSpecial(env.lang),
        arg->getType(),
        param->type,
        false /*destIsReceiver*/);
      if (!ic) {
        env.error(arg->getType(), stringc
          << "cannot convert argument type `" << arg->getType()->toString()
          << "' to parameter " << paramIndex 
          << " type `" << param->type->toString() << "'");
      }

      // TODO (elaboration): if 'ic' involves a user-defined
      // conversion, then modify the AST to make that explicit

      // at least note that we plan to use this conversion, so
      // if it involves template functions, instantiate them
      env.instantiateTemplatesInConversion(ic);
    }
  }

  if (argIter->isEmpty()) {
    // check that all remaining parameters have default arguments
    for (; !paramIter.isDone(); paramIter.adv(), paramIndex++) {
      if (!paramIter.data()->value) {
        env.error(stringc
          << "no argument supplied for parameter " << paramIndex);
      }
      else {
        // TODO (elaboration): modify the call site to explicitly
        // insert the default-argument expression (is that possible?
        // might it run into problems with evaluation contexts?)
        defaultArgsUsed++;
      }
    }
  }
  else if (paramIter.isDone() && !ft->acceptsVarargs()) {
    env.error("too many arguments supplied");
  }
  
  return defaultArgsUsed;
}

void compareCtorArgsToParams(Env &env, Variable *ctor,
                             FakeList<ArgExpression> *args,
                             ArgumentInfoArray &argInfo)
{
  env.ensureFuncBodyTChecked(ctor);

  if (ctor) {
    int defaultArgsUsed = compareArgsToParams(env, ctor->type->asFunctionType(),
                                              args, argInfo);
    if (defaultArgsUsed) {
      env.instantiateDefaultArgs(ctor, defaultArgsUsed);
    }
  }
}


static bool hasNamedFunction(Expression *e)
{
  return e->isE_variable() || e->isE_fieldAcc();
}

static Variable *getNamedFunction(Expression *e)
{
  if (e->isE_variable()) { return e->asE_variable()->var; }
  if (e->isE_fieldAcc()) { return e->asE_fieldAcc()->field; }
  xfailure("no named function");
  return NULL;   // silence warning
}
  
// fwd
static Type *internalTestingHooks
  (Env &env, StringRef funcName, FakeList<ArgExpression> *args);


// true if the type has no destructor because it's not a compound type
// nor an array of (an array of ..) compound types
static bool hasNoopDtor(Type *t)
{
  // if it's an array type, then whether it has a no-op dtor depends
  // entirely on whether the element type has a no-op dtor
  while (t->isArrayType()) {
    t = t->asArrayType()->eltType;
  }

  return !t->isCompoundType();
}

Type *E_funCall::itcheck_x(Env &env, Expression *&replacement)
{
  LookupSet candidates;
  inner1_itcheck(env, candidates);

  // special case: if someone explicitly called the destructor
  // of a non-class type, e.g.:
  //   typedef unsigned uint;
  //   uint x;
  //   x.~uint();
  // then change it into a void-typed simple evaluation:
  //   (void)x;
  // since the call itself is a no-op
  if (func->isE_fieldAcc()) {
    E_fieldAcc *fa = func->asE_fieldAcc();
    if (fa->fieldName->getName()[0] == '~' &&
        hasNoopDtor(fa->obj->type->asRval())) {
      if (args->isNotEmpty()) {
        env.error("call to dtor must have no arguments");
      }
      ASTTypeId *voidId =
        new ASTTypeId(new TS_simple(SL_UNKNOWN, SL_UNKNOWN, ST_VOID),
                      new Declarator(new D_name(SL_UNKNOWN, NULL /*name*/),
                                     NULL /*init*/));
      replacement = new E_cast(voidId, fa->obj);
      replacement->tcheck(env, replacement);
      return replacement->type;
    }
  }

  return inner2_itcheck(env, candidates);
}

void E_funCall::inner1_itcheck(Env &env, LookupSet &candidates)
{
  // dsw: I need to know the arguments before I'm asked to instantiate
  // the function template
  //
  // check the argument list
  //
  // sm: No!  That defeats the entire purpose of inner1/2.  See the
  // comments above the block that calls inner1/2, and the comments
  // near the declarations of inner1/2 in cc_tcheck.ast.
  //args = tcheckArgExprList(args, env);

  // 2005-02-11: Doing this simplifies a number of things.  In general
  // I think I should move towards a strategy of eliminating
  // E_groupings wherever I can do so.  Eventually, I'd like it to be
  // the case that no E_groupings survive type checking.
  func = func->skipGroups();

  // nominal flags if we're calling a named function
  LookupFlags specialFlags =
    LF_TEMPL_PRIMARY |       // we will do template instantiation later
    LF_FUNCTION_NAME |       // we might allow an implicit declaration
    LF_NO_IMPL_THIS ;        // don't add 'this->' (must do overload resol'n first)

  if (func->isE_variable() &&
      !func->asE_variable()->name->hasQualifiers()) {
      // Unqualified name being looked up in the context of a function
      // call; cppstd 3.4.2 applies, which is implemented in
      // inner2_itcheck.  So, here, we don't report an error because
      // inner2 will do another lookup and report an error if that one
      // fails too.
      specialFlags |= LF_SUPPRESS_NONEXIST;
  }
  
  // tcheck, passing candidates if possible
  tcheckExpression_set(env, func, specialFlags, candidates);
}


bool hasDependentTemplateArgs(PQName *name)
{
  // I think I only want to look at the final component
  name = name->getUnqualifiedName();
  
  if (name->isPQ_template()) {
    return containsVariables(name->asPQ_template()->sargs);
  }

  return false;
}

void possiblyWrapWithImplicitThis(Env &env, Expression *&func,
                                  E_variable *&fevar, E_fieldAcc *&feacc)
{
  if (fevar &&
      fevar->var &&
      fevar->var->isMember() &&
      !fevar->var->isStatic()) {
    feacc = wrapWithImplicitThis(env, fevar->var, fevar->name);
    func = feacc;
    fevar = NULL;
  }
}

Type *E_funCall::inner2_itcheck(Env &env, LookupSet &candidates)
{
  // inner1 skipped E_groupings already
  xassert(!func->isE_grouping());

  // is 'func' an E_variable?  a number of special cases kick in if so
  E_variable *fevar = func->isE_variable()? func->asE_variable() : NULL;

  // similarly for E_fieldAcc
  E_fieldAcc *feacc = func->isE_fieldAcc()? func->asE_fieldAcc() : NULL;
                       
  // if a method is being invoked, what is the type of the receiver
  // object?  (may be NULL if none is available)
  Type *receiverType = feacc? feacc->obj->type : env.implicitReceiverType();

  // check the argument list
  ArgumentInfoArray argInfo(args->count() + 1);
  args = tcheckArgExprList(args, env, argInfo, receiverType);

  // for internal testing
  if (fevar) {
    Type *ret = internalTestingHooks(env, fevar->name->getName(), args);
    if (ret) {
      return ret;
    }
  }

  // do any of the arguments have types that are dependent on template params?
  bool dependentArgs = hasDependentActualArgs(args);

  // what about explicitly-provided template args that are dependent?
  if (fevar && hasDependentTemplateArgs(fevar->name)) {
    dependentArgs = true;
  }
  if (feacc && hasDependentTemplateArgs(feacc->fieldName)) {
    dependentArgs = true;
  }

  // abbreviated processing for dependent lookups
  if (dependentArgs) {
    if (fevar && fevar->nondependentVar) {
      // kill the 'nondependent' lookup
      TRACE("dependent", toString(fevar->name->loc) <<
        ": killing the nondependency of " << fevar->nondependentVar->name);
      fevar->nondependentVar = NULL;
    }

    // 14.6.2 para 1, 14.6.2.2 para 1
    return env.dependentType();
  }
  else if (feacc && feacc->type->isGeneralizedDependent()) {
    return env.dependentType();
  }

  // did we already decide to re-use a previous nondependent lookup
  // result?  (in/t0387.cc)
  bool const alreadyDidLookup =
    !env.inUninstTemplate() &&
    fevar && 
    fevar->nondependentVar && 
    fevar->nondependentVar == fevar->var;

  // 2005-02-18: rewrote function call site name lookup; see doc/lookup.txt
  if (env.lang.allowOverloading &&
      !alreadyDidLookup &&
      (func->type->isSimple(ST_NOTFOUND) ||
       func->type->asRval()->isFunctionType()) &&
      (fevar || (feacc &&
                 // in the case of a call to a compiler-synthesized
                 // destructor, the 'field' is currently NULL (that might
                 // change); but in that case overloading is not possible,
                 // so this code can safely ignore it (e.g. in/t0091.cc)
                 feacc->field))) {
    PQName *pqname = fevar? fevar->name : feacc->fieldName;

    // what is the set of names obtained by inner1?
    //LookupSet candidates;   // use passed-in list

    // augment with arg-dep lookup?
    if (fevar &&                                // E_variable,
        !pqname->hasQualifiers() &&             // unqualified,
        (fevar->type->isSimple(ST_NOTFOUND) ||  // orig lookup failed
         !fevar->var->isMember())) {            //   or found a nonmember 
      // get additional candidates from associated scopes
      ArrayStack<Type*> argTypes(args->count());
      FAKELIST_FOREACH(ArgExpression, args, iter) {
        argTypes.push(iter->getType());
      }
      env.associatedScopeLookup(candidates, pqname->getName(),
                                argTypes, LF_NONE);
    }

    if (candidates.isEmpty()) {
      if (env.annotating) {
        // bhackett: TODO: should only see builtin annotation functions here.
        return env.errorType();
      }
      else {
        return fevar->type =
          env.error(pqname->loc,
                    stringc << "there is no function called `"
                            << pqname->getName() << "'"
                            << env.unsearchedDependentBases(),
                    EF_NONE);
      }
    }

    // template args supplied?
    PQ_template *targs = NULL;
    if (pqname->getUnqualifiedName()->isPQ_template()) {
      targs = pqname->getUnqualifiedName()->asPQ_template();
    }

    // refine candidates by instantiating templates, etc.
    char const *lastRemovalReason = "(none removed yet)";
    SObjListMutator<Variable> mut(candidates);
    while (!mut.isDone()) {
      Variable *v = mut.data();
      bool const considerInherited = false;
      InferArgFlags const iflags = IA_NO_ERRORS;

      // filter out non-templates if we have template arguments
      if (targs && !v->isTemplate(considerInherited)) {
        mut.remove();
        lastRemovalReason = "non-template given template arguments";
        continue;
      }

      // instantiate templates
      if (v->isTemplate(considerInherited)) {
        // initialize the bindings with those explicitly provided
        MType match(env);
        if (targs) {
          if (!env.loadBindingsWithExplTemplArgs(v, targs->sargs, match, iflags)) {
            mut.remove();
            lastRemovalReason = "incompatible explicit template args";
            continue;
          }
        }

        // deduce the rest from the call site (expression) args
        TypeListIter_FakeList argsIter(args);
        if (!env.inferTemplArgsFromFuncArgs(v, argsIter, match, iflags)) {
          mut.remove();
          lastRemovalReason = "incompatible call site args";
          continue;
        }

        // use them to instantiate the template
        Variable *inst = env.instantiateFunctionTemplate(pqname->loc, v, match);
        if (!inst) {
          mut.remove();
          lastRemovalReason = "could not deduce all template params";
          continue;
        }

        // replace the template primary with its instantiation
        mut.dataRef() = inst;
      }
      
      mut.adv();
    }

    // do we still have any candidates?
    if (candidates.isEmpty()) {
      return env.error(pqname->loc, stringc
               << "call site name lookup failed to yield any candidates; "
               << "last candidate was removed because: " << lastRemovalReason);
    }

    // throw the whole mess at overload resolution
    Variable *chosen;
    if (candidates.count() > 1) {
      // pick the best candidate
      chosen = outerResolveOverload_explicitSet
        (env, pqname, pqname->loc, pqname->getName(),
         argInfo, candidates);
    }
    else {
      chosen = candidates.first();
    }

    if (chosen) {
      // rewrite AST to reflect choice
      //
      // the stored type will be the dealiased type in hopes this
      // achieves 7.3.3 para 13, "This has no effect on the type of
      // the function, and in all other respects the function
      // remains a member of the base class."
      chosen = env.storeVar(chosen);
      if (fevar) {
        fevar->var = chosen;
        maybeNondependent(env, pqname->loc, fevar->nondependentVar, chosen);   // in/t0385.cc
      }
      else {
        feacc->field = chosen;

        // TODO: I'm pretty sure I need nondependent names for E_fieldAcc too
        //maybeNondependent(env, pqname->loc, feacc->nondependentVar, chosen);
      }
      func->type = chosen->type;
    }
    else {
      return env.errorType();
    }
  }

  // the type of the function that is being invoked
  Type *t = func->type->asRval();

  // check for operator()
  CompoundType *ct = t->ifCompoundType();
  if (ct) {
    // the insertion of implicit 'this->' below will not be reached,
    // so do it here too
    possiblyWrapWithImplicitThis(env, func, fevar, feacc);

    env.ensureCompleteType("use as function object", t);
    Variable *funcVar = ct->getNamedField(env.functionOperatorName, env);
    if (funcVar) {
      // resolve overloading
      getArgumentInfo(env, argInfo[0], func);
      funcVar = outerResolveOverload(env, NULL /*finalName*/, env.loc(), funcVar,
                                     argInfo);
      if (funcVar) {
        // rewrite AST to reflect use of 'operator()'
        Expression *object = func;
        E_fieldAcc *fa = new E_fieldAcc(object,
          new PQ_operator(SL_UNKNOWN, new ON_operator(OP_PARENS), env.functionOperatorName));
        fa->field = funcVar;
        fa->type = funcVar->type;
        func = fa;

        return funcVar->type->asFunctionType()->retType;
      }
      else {
        return env.errorType();
      }
    }
    else {
      return env.error(stringc
        << "object of type `" << t->toString() << "' used as a function, "
        << "but it has no operator() declared");
    }
  }

  // fulfill the promise that inner1 made when it passed
  // LF_NO_IMPL_THIS, namely that we would add 'this->' later
  // if needed; here is "later"
  possiblyWrapWithImplicitThis(env, func, fevar, feacc);

  // make sure this function has been typechecked
  if (fevar) {
    // if it is a pointer to a function that function should get
    // instantiated when its address is taken
    env.ensureFuncBodyTChecked(fevar->var);
  }
  else if (feacc) {
    env.ensureFuncBodyTChecked(feacc->field);
  }

  // automatically coerce function pointers into functions
  if (t->isPointerType()) {
    t = t->asPointerTypeC()->atType;
    // if it is an E_variable then its overload set will be NULL so we
    // won't be doing overload resolution in this case
  }

  if (t->isGeneralizedDependent()) {
    return env.dependentType();      // in/k0021.cc
  }

  if (!t->isFunctionType()) {
    return env.error(t, stringc
      << "you can't use an expression of type `" << t->toString()
      << "' as a function");
  }

  FunctionType *ft = t->asFunctionType();
  env.instantiateTemplatesInParams(ft);
  env.ensureCompleteType("use as return type in invoked function", ft->retType);

  // receiver object?
  if (env.doCompareArgsToParams && ft->isMethod()) {
    Type *receiverType = NULL;
    if (feacc) {
      // explicit receiver via '.'
      receiverType = feacc->obj->type;
    }
    else if (func->isE_binary() &&
             func->asE_binary()->op == BIN_DOT_STAR) {
      // explicit receiver via '.*'
      receiverType = func->asE_binary()->e1->type;
    }
    else if (func->isE_binary() &&
             func->asE_binary()->op == BIN_ARROW_STAR) {
      // explicit receiver via '->*'
      receiverType = func->asE_binary()->e1->type->asRval();

      // if this weren't true, then the type checker for '->*' would
      // already have indicated the error and assigned the ST_ERROR
      // type, so 't' would not be a FunctionType
      xassert(receiverType->isPointerType());

      receiverType = receiverType->asPointerType()->atType;
    }
    else {        // gcov-ignore
      // now that we wrap with 'this->' explicitly, this code should
      // not be reachable
      xfailure("got to implicit receiver code; should not be possible!");
    }

    if (receiverType) {
      // 12.4p2: it is legal to invoke a destructor on an object that
      // is const or volatile, and dtors never have such qualifiers,
      // so if we are invoking a dtor then remove the qualifiers
      if (ft->isDestructor() &&
          receiverType->asRval()->getCVFlags() != CV_NONE) {
        bool wasRef = receiverType->isReference();
        receiverType = receiverType->asRval();
        receiverType = env.tfac.setQualifiers(SL_UNKNOWN, CV_NONE, receiverType, NULL /*syntax*/);
        if (wasRef) {
          receiverType = env.tfac.makeReferenceType(receiverType);
        }
      }

      // check that the receiver object matches the receiver parameter
      if (!getImplicitConversion(env,
             SE_NONE,
             receiverType,
             ft->getReceiver()->type,
             true /*destIsReceiver*/)) {
        env.error(stringc
          << "cannot convert argument type `" << receiverType->toString()
          << "' to receiver parameter type `" << ft->getReceiver()->type->toString()
          << "'");
      }
    }
    else {
      // error already reported
    }
  }

  // compare argument types to parameters (not guaranteed by overload
  // resolution since it might not have been done, and even if done,
  // uses more liberal rules)
  int defaultArgsUsed = compareArgsToParams(env, ft, args, argInfo);

  // instantiate default args
  if (defaultArgsUsed) {
    if (fevar) {
      env.instantiateDefaultArgs(fevar->var, defaultArgsUsed);
    }
    else if (feacc) {
      env.instantiateDefaultArgs(feacc->field, defaultArgsUsed);
    }
  }

  // type of the expr is type of the return value
  return ft->retType;
}


// special hooks for testing internal algorithms; returns a type
// for the entire E_funCall expression if it recognizes the form
// and typechecks it in its entirety
//
// actually, the arguments have already been tchecked ...
static Type *internalTestingHooks
  (Env &env, StringRef funcName, FakeList<ArgExpression> *args)
{
  // check the type of an expression
  if (funcName == env.special_checkType) {
    if (args->count() == 2) {
      Type *t1 = args->nth(0)->getType();
      Type *t2 = args->nth(1)->getType();
      if (t1->equals(t2)) {
        // ok
      }
      else {
        env.error(stringc << "checkType: `" << t1->toString() 
                          << "' != `" << t2->toString() << "'");
      }
    }
    else {
      env.error("invalid call to __checkType");
    }
  }

  // test vector for 'getStandardConversion'
  if (funcName == env.special_getStandardConversion) {
    int expect;
    if (args->count() == 3 &&
        args->nth(2)->constEval(env, expect)) {
      test_getStandardConversion
        (env,
         args->nth(0)->getSpecial(env.lang),     // is it special?
         args->nth(0)->getType(),                // source type
         args->nth(1)->getType(),                // dest type
         expect);                                // expected result
    }
    else {
      env.error("invalid call to __getStandardConversion");
    }
  }

  // test vector for 'getImplicitConversion'
  if (funcName == env.special_getImplicitConversion) {
    int expectKind;
    int expectSCS;
    int expectUserLine;
    int expectSCS2;
    if (args->count() == 6 &&
        args->nth(2)->constEval(env, expectKind) &&
        args->nth(3)->constEval(env, expectSCS) &&
        args->nth(4)->constEval(env, expectUserLine) &&
        args->nth(5)->constEval(env, expectSCS2)) {
      test_getImplicitConversion
        (env,
         args->nth(0)->getSpecial(env.lang),     // is it special?
         args->nth(0)->getType(),                // source type
         args->nth(1)->getType(),                // dest type
         expectKind, expectSCS, expectUserLine, expectSCS2);   // expected result
    }
    else {
      env.error("invalid call to __getImplicitConversion");
    }
  }

  // test overload resolution
  if (funcName == env.special_testOverload) {
    int expectLine;
    if (args->count() == 2 &&
        args->nth(1)->constEval(env, expectLine)) {

      if (args->first()->expr->isE_funCall() &&
          hasNamedFunction(args->first()->expr->asE_funCall()->func)) {
        // resolution yielded a function call
        Variable *chosen = getNamedFunction(args->first()->expr->asE_funCall()->func);
        int actualLine = sourceLocManager->getLine(chosen->loc);
        if (expectLine != actualLine) {
          env.error(stringc
            << "expected overload to choose function on line "
            << expectLine << ", but it chose line " << actualLine,
            EF_STRONG);
        }
      }
      else if (expectLine != 0) {
        // resolution yielded something else
        env.error("expected overload to choose a function, but it "
                  "chose a non-function");
      }

      // propagate return type
      return args->first()->getType();
    }
    else {
      env.error("invalid call to __testOverload");
    }
  }

  // test vector for 'computeLUB'
  if (funcName == env.special_computeLUB) {
    int expect;
    if (args->count() == 4 &&
        args->nth(3)->constEval(env, expect)) {
      test_computeLUB
        (env,
         args->nth(0)->getType(),        // T1
         args->nth(1)->getType(),        // T2
         args->nth(2)->getType(),        // LUB
         expect);                        // expected result
    }
    else {
      env.error("invalid call to __computeLUB");
    }
  }

  // given a call site, check that the function it calls is
  // (a) defined, and (b) defined at a particular line
  if (funcName == env.special_checkCalleeDefnLine) {
    int expectLine;
    if (args->count() == 2 &&
        args->nth(1)->constEval(env, expectLine)) {

      if (args->first()->expr->isE_funCall() &&
          hasNamedFunction(args->first()->expr->asE_funCall()->func)) {
        // resolution yielded a function call
        Variable *chosen = getNamedFunction(args->first()->expr->asE_funCall()->func);
        if (!chosen->funcDefn) {
          env.error("expected to be calling a defined function");
        }
        else {
          int actualLine = sourceLocManager->getLine(chosen->funcDefn->getLoc());
          if (expectLine != actualLine) {
            env.error(stringc
              << "expected to call function on line "
              << expectLine << ", but it chose line " << actualLine);
          }
        }
      }
      else if (expectLine != 0) {
        // resolution yielded something else
        env.error("expected overload to choose a function, but it "
                  "chose a non-function");
      }

      // propagate return type
      return args->first()->getType();
    }
    else {
      env.error("invalid call to __checkCalleeDefnLine");
    }
  }

  
  // syntax of calls to __test_mtype:
  //
  // Form 1: match is expected to succeed
  //
  //   __test_mtype((C)0, (P)0, FLAGS,
  //                "A", (T1)0,           // form of type bindings
  //                "n", 3,               // form of value bindings
  //                ...                   // remaining binding pairs
  //               );
  //
  //   where C is the concrete type, P is the pattern type, FLAGS
  //   is a bitwise OR of MatchFlags, T1 is the proposed type binding
  //   for variable "A", and 3 is the expected value of variable "n".
  //
  // Form 2: match is expected fo fail
  //
  //   __test_mtype((C)0, (P)0, FLAGS, false);     // four args total
  //
  if (funcName == env.special_test_mtype) {
    int nArgs = args->count();
    if (nArgs < 3) {
      return env.error("__test_mtype requires at least three arguments");
    }

    Type *conc = args->nth(0)->getType();
    Type *pat = args->nth(1)->getType();
    int flags;
    if (!args->nth(2)->constEval(env, flags)) {
      return env.error("third argument to __test_mtype must be a constant expression");
    }
    if (flags & ~MF_ALL) {
      return env.error("invalid flags value for __test_mtype");
    }
    bool expectSuccess = (nArgs != 4);
    if (expectSuccess && (nArgs%2 != 1)) {
      return env.error("__test_mtype requires either four or an odd number of arguments");
    }

    MType mtype(env);
    if (mtype.matchTypeNC(conc, pat, (MatchFlags)flags)) {
      if (expectSuccess) {
        // successed as expected; check the bindings
        int i;
        for (i=0; (i+1)*2+1 < nArgs; i++) {
          Expression *name = args->nth((i+1)*2+1)->expr;
          Expression *value = args->nth((i+1)*2+2)->expr;

          // 'name' should be a string literal naming a variable in 'pat'
          if (!name->isE_stringLit()) {
            return env.error(stringc << "__test_mtype argument " << (i+1)*2+1+1
                                     << " must be a string literal");
          }
          StringRef nameStr = env.str(parseQuotedString(name->asE_stringLit()->text));

          // it should correspond to an existing binding in 'mtype'
          STemplateArgument binding(mtype.getBoundValue(nameStr, env.tfac));
          if (!binding.hasValue()) {
            return env.error(stringc << "__test_mtype: " << nameStr << " is not bound");
          }

          // we interpret 'value' depending on what kind of thing is
          // the 'binding', and hope this won't mask any problems
          switch (binding.kind) {
            default:
              return env.error(stringc << "unexpected binding kind: "
                                       << toString(binding.kind));

            case STemplateArgument::STA_TYPE:
              if (!binding.getType()->equals(value->getType())) {
                return env.error(stringc << "__test_mtype: "
                  << "expected " << nameStr
                  << " to be bound to `" << value->getType()->toString()
                  << "' but it was actually bound to `"
                  << binding.getType()->toString() << "'");
              }
              break;

            case STemplateArgument::STA_INT: {
              int valueInt;
              if (!value->constEval(env, valueInt)) {
                return env.error(stringc << "__test_mtype: "
                  << nameStr << " was bound to an int, but the provided "
                  << "expression is not a constant");
              }
              if (valueInt != binding.getInt()) {
                return env.error(stringc << "__test_mtype: "
                  << "expected " << nameStr
                  << " to be bound to " << valueInt
                  << " but it was actually bound to "
                  << binding.getInt());
              }
              break;
            }
          }
        } // end of loop over supplied bindings
        
        // the user should have supplied as many bindings as there
        // are bindings in 'mtype'
        if (mtype.getNumBindings() != i) {
          return env.error(stringc << "__test_mtype: "
            << "call site supplied " << pluraln(i , "binding") 
            << ", but match yielded " << mtype.getNumBindings());
        }
      }
      else {
        return env.error("mtype succeeded, but failure was expected");
      }
    }
    else {
      if (expectSuccess) {
        return env.error("mtype failed, but success was expected");
      }
      else {
        // failed as expected
      }
    }

    return env.getSimpleType(ST_VOID);
  }

  // The purpose of this is to be able to exercise some of the error
  // handling paths.
  if (funcName == env.special_cause_xfailure) {
    xfailure("program contains __cause_xfailure");
  }

  // E_funCall::itcheck should continue, and tcheck this normally
  return NULL;
}


Type *E_constructor::itcheck_x(Env &env, Expression *&replacement)
{
  inner1_itcheck(env);

  return inner2_itcheck(env, replacement);
}

void E_constructor::inner1_itcheck(Env &env)
{
  type = spec->tcheck(env, DF_NONE);
}

Type *E_constructor::inner2_itcheck(Env &env, Expression *&replacement)
{
  xassert(replacement == this);

  // inner1_itcheck sets the type, so if it signaled an error then bail
  if (type->isError()) {
    return type;
  }

  // check arguments
  ArgumentInfoArray argInfo(args->count() + 1);
  args = tcheckArgExprList(args, env, argInfo);

  if (!env.ensureCompleteType("construct", type)) {
    return type;     // recovery: skip what follows
  }

  // simplify some gratuitous uses of E_constructor
  if (!type->isLikeCompoundType() && !type->isGeneralizedDependent()) {
    // you can make a temporary for an int like this (from
    // in/t0014.cc)
    //   x = int(6);
    // or you can use a typedef to get any other type like this (from
    // t0059.cc)
    //   typedef char* char_ptr;
    //   typedef unsigned long ulong;
    //   return ulong(char_ptr(mFragmentIdentifier)-char_ptr(0));
    // in those cases, there isn't really any ctor to call, so just
    // turn it into a cast

    // there had better be exactly one argument to this ctor
    //
    // oops.. actually there can be zero; "int()" is valid syntax,
    // yielding an integer with indeterminate value
    //
    // 2005-05-28: (in/t0495.cc) count the args *after* tchecking them
    if (args->count() > 1) {
      return env.error(stringc
        << "function-style cast to `" << type->toString()
        << "' must have zere or one argument (not "
        << args->count() << ")");
    }

    // change it into a cast; this code used to do some 'buildASTTypeId'
    // contortions, but that's silly since the E_constructor already
    // carries a perfectly good type specifier ('this->spec'), and so
    // all we need to do is add an empty declarator
    ASTTypeId *typeSyntax = new ASTTypeId(this->spec,
      new Declarator(new D_name(this->spec->loc, NULL /*name*/), NULL /*init*/));
    if (args->count() == 1) {
      replacement =
        new E_cast(typeSyntax, args->first()->expr);
    }
    else {   /* zero args */
      // The correct semantics (e.g. from a verification point of
      // view) would be to yield a value about which nothing is known,
      // but there is no simple way to do that in the existing AST.  I
      // just want to hack past this for now, since I think it will be
      // very unlikely to cause a real problem, so my solution is to
      // pretend it's always the value 0.
      replacement =
        new E_cast(typeSyntax, env.build_E_intLit(0));
    }
    replacement->tcheck(env, replacement);
    return replacement->type;
  }

  Variable *ctor = outerResolveOverload_ctor(env, env.loc(), type, argInfo);
  ctorVar = env.storeVar(ctor);
  compareCtorArgsToParams(env, ctor, args, argInfo);

  return type;
}


// Maybe this should go in variable.h?  If so, I should be more careful
// to ensure the case analysis is exhaustive.
string kindAndType(Variable *v)
{
  if (v->isNamespace()) {
    return stringc << "namespace " << v->fullyQualifiedName();
  }
  else if (v->isType()) {
    if (v->type->isCompoundType()) {
      CompoundType *ct = v->type->asCompoundType();
      return stringc << toString(ct->keyword) << " " << v->fullyQualifiedName();
    }
    else {
      return stringc << "type `" << v->type->toString() << "'";
    }
  }
  else if (v->type->isFunctionType()) {
    return stringc << "function of type `" << v->type->toString() << "'";
  }
  else {
    return stringc << "object of type `" << v->type->toString() << "'";
  }
}


PQ_qualifier *getSecondToLast(PQ_qualifier *name)
{
  while (name->rest->isPQ_qualifier()) {
    name = name->rest->asPQ_qualifier();
  }
  return name;
}

 
// do 'var1' and 'var2' refer to the same class type,
// as required by 3.4.5p3?
bool sameCompounds(Variable *var1, Variable *var2)
{
  CompoundType *ct1 = var1->type->asCompoundType();
  CompoundType *ct2 = var2->type->asCompoundType();
  if (ct1 == ct2) {
    return true;      // easy case
  }
  
  // in/t0481.cc contains an interesting variation where one of the
  // variables refers to a template, and the other to an instantiation
  // of that template, through no fault of the programmer.  Since both
  // gcc and icc accept it, I will too, even though a strict reading
  // of the standard seems to suggest the opposite.
  TemplateInfo *ti1 = ct1->templateInfo();
  TemplateInfo *ti2 = ct2->templateInfo();
  if (ti1 && ti2 &&                                 // both are template things
      (ti1->isPrimary() || ti2->isPrimary()) &&     // one is the primary
      ti1->getPrimary() == ti2->getPrimary()) {     // other is specialization
    return true;
  }
  
  return false;
}

bool findAnonymousField(Env &env, CompoundType *ct,
                        PQName *fieldName,
                        ArrayStack<Variable*> &anon_fields)
{
  for (int ind = 0; ind < ct->dataMembers.count(); ind++) {
    Variable *field = ct->dataMembers.nth(ind);

    if (field->type->isCompoundType()) {
      CompoundType *fct = field->type->asCompoundType();

      // recognize the anonymous names generated by env.getAnonName().
      if (strncmp(fct->name, "__anon_", 7) == 0) {

        // check to see if we are looking for the anonymous struct/union
        // itself, since it doesn't show up in the scope for the structure.
        if (field->name == fieldName->getName()) {
          xassert(anon_fields.isEmpty());
          anon_fields.push(field);
          return true;
        }

        // check for a matching field within the anonymous struct/union.
        LookupSet candidates;
        env.unqualifiedFinalNameLookup(candidates, fct, fieldName, LF_NONE);
        if (!candidates.isEmpty()) {
          xassert(anon_fields.isEmpty());
          Variable *f = candidates.first();
          anon_fields.push(env.storeVar(f));
          anon_fields.push(field);
          return true;
        }

        // try recursing, the anonymous field could contain more anonymous
        // struct/union fields.
        if (findAnonymousField(env, fct, fieldName, anon_fields)) {
          anon_fields.push(field);
          return true;
        }
      }
    }
  }

  return false;
}

// cppstd sections: 5.2.4, 5.2.5 and 3.4.5
Type *E_fieldAcc::itcheck_x(Env &env, Expression *&replacement)
{
  return itcheck_fieldAcc(env, LF_NONE);
}

Type *E_fieldAcc::itcheck_fieldAcc(Env &env, LookupFlags flags)
{
  LookupSet dummy;
  return itcheck_fieldAcc_set(env, flags, dummy);
}

Type *E_fieldAcc::itcheck_fieldAcc_set(Env &env, LookupFlags flags,
                                       LookupSet &candidates)
{
  obj->tcheck(env, obj);

  // tcheck template arguments and ON_conversion types in the
  // current scope
  tcheckPQName(fieldName, env, NULL /*scope*/, LF_NONE);

  // want this generally I think
  flags |= LF_SELFNAME;

  // naming a destructor?
  StringRef rhsFinalTypeName = fieldName->getName();
  bool isDestructor = rhsFinalTypeName[0] == '~';
  if (isDestructor) {
    rhsFinalTypeName = env.str(rhsFinalTypeName+1);    // skip '~'
  }

  // component of a __complex__ type?
  #ifdef GNU_EXTENSION
  if (rhsFinalTypeName == env.string_realSelector ||
      rhsFinalTypeName == env.string_imagSelector) {
    return itcheck_complex_selector(env, flags, candidates);
  }
  #endif // GNU_EXTENSION

  // dependent?
  if (obj->type->containsGeneralizedDependent()) {
    if (isDestructor) {
      // 14.6.2.2 para 4; type is function accepting nothing and
      // returning void
      FunctionType *ft = env.tfac.makeFunctionType(env.getSimpleType(ST_VOID));
      env.tfac.doneParams(ft);
      return ft;
    }
    else {
      // 14.6.2.2 para 1
      return env.dependentType();
    }
  }

  // get the type of 'obj', and check if is a compound
  Type *lhsType = obj->type->asRval();
  CompoundType *ct = lhsType->ifCompoundType();
  if (!ct) {
    // 5.2.4: pseudo-destructor
    if (!isDestructor ||
        !fieldName->getUnqualifiedName()->isPQ_name()) {
      return env.error(lhsType, fieldName->loc, stringc
        << "RHS of . or -> must be of the form \"~ identifier\" if the LHS "
        << "is not a class; the LHS is `" << lhsType->toString() << "'");
    }

    // this will be set to the type of the RHS
    Type *rhsType = NULL;

    if (fieldName->hasQualifiers()) {
      // get pointers to the last three elements in the name
      PQ_qualifier *thirdLast=NULL, *secondLast=NULL;
      PQName *last = fieldName;
      while (last->isPQ_qualifier()) {
        // shift
        thirdLast = secondLast;
        secondLast = last->asPQ_qualifier();
        last = secondLast->rest;
      }
      xassert(secondLast);

      if (secondLast->sargs.isNotEmpty()) {
        return env.error(fieldName->loc, "cannot have templatized qualifier as "
          "second-to-last element of RHS of . or -> when LHS is not a class");
      }

      // these will be set to the lookup results of secondLast and last, resp.
      Variable *secondVar = NULL;
      Variable *lastVar = NULL;

      if (!thirdLast) {
        // 'fieldName' must be of form type-name :: ~ type-name, so
        // we do unqualified lookups
        xassert(secondLast->qualifier);   // grammar should ensure this
        secondVar = env.unqualifiedLookup_one(secondLast->qualifier,
          /* the name precedes "::" so ... */ LF_QUALIFIER_LOOKUP);
        lastVar = env.unqualifiedLookup_one(rhsFinalTypeName, flags);
      }

      else {
        // 'fieldName' of form Q :: type-name1 :: ~ type-name2, and so
        // *both* lookups are to be done as if qualified by
        // 'thirdLast'; to accomplish this, temporarily modify
        // 'thirdLast' to construct the needed names

        // fieldName := Q :: type-name1
        PQ_name fakeLast(secondLast->loc, secondLast->qualifier);
        thirdLast->rest = &fakeLast;
        secondVar = env.lookupPQ_one(fieldName, flags | LF_QUALIFIER_LOOKUP);

        // fieldName := Q :: type-name2
        fakeLast.loc = last->loc;
        fakeLast.name = rhsFinalTypeName;
        lastVar = env.lookupPQ_one(fieldName, flags);

        // fieldName := original fieldName
        thirdLast->rest = secondLast;
      }

      if (!secondVar || !secondVar->isType()) {
        PQName *n = getSecondToLast(fieldName->asPQ_qualifier());
        return env.error(n->loc, stringc
          << "no such type: `" << n->toComponentString() << "'");
      }
      if (!lastVar || !lastVar->isType()) {
        PQName *n = fieldName->getUnqualifiedName();
        return env.error(n->loc, stringc
          << "no such type: `" << n->toComponentString() << "'");
      }
      if (!lastVar->type->equals(secondVar->type)) {
        return env.error(fieldName->loc, stringc
          << "in . or -> expression, when LHS is non-class type "
          << "(its type is `" << lhsType->toString() << "'), a qualified RHS "
          << "must be of the form Q :: t1 :: ~t2 where t1 and t2 are "
          << "the same type, but t1 is `" << secondVar->type->toString()
          << "' and t2 is `" << lastVar->type->toString() << "'");
      }
      rhsType = lastVar->type;
    }

    else {
      // RHS of form ~ type-name
      Variable *v = env.unqualifiedLookup_one(rhsFinalTypeName, flags);
      if (!v || !v->hasFlag(DF_TYPEDEF)) {
        return env.error(fieldName->loc,
          stringc << "no such type: `" << rhsFinalTypeName << "'");
      }
      rhsType = v->type;
    }

    if (!lhsType->equals(rhsType, MF_IGNORE_TOP_CV)) {
      return env.error(fieldName->loc, stringc
        << "in . or -> expression, when LHS is non-class type, its type "
        << "must be the same (modulo cv qualifiers) as the RHS; but the "
        << "LHS type is `" << lhsType->toString() << "' and the RHS type is `"
        << rhsType->toString() << "'");
    }

    // pseudo-destructor invocation
    //
    // an older comment read:
    //   invoking destructor explicitly, which is allowed for all
    //   types; most of the time, the rewrite in E_funCall::itcheck
    //   will replace this, but in the case of a type which is an
    //   array of objects, this will leave the E_fieldAcc's 'field'
    //   member NULL ...
    return env.makeDestructorFunctionType(SL_UNKNOWN, NULL /*ct*/);
  }

  // make sure the type has been completed
  if (!env.ensureCompleteType("access a member of", lhsType)) {
    return env.errorType();
  }

  // I'm just going to say that any field access that involves
  // a dependent type is itself of dependent type
  #define HANDLE_DEPENDENT(v)                                     \
    if (v && v->type && v->type->isGeneralizedDependent()) {      \
      return env.dependentType();                                 \
    }

  // case analysis on the presence/kind of qualifiers
  if (fieldName->isPQ_qualifier() &&
      fieldName->asPQ_qualifier()->qualifier == NULL) {
    // global scope qualifier: 3.4.5p5
    env.lookupPQ(candidates, fieldName, flags);
  }

  else if (fieldName->isPQ_qualifier()) {
    // qualified (but not global scope): 3.4.5p4
    PQ_qualifier *firstQ = fieldName->asPQ_qualifier();

    // unqualified lookup of firstQ
    Variable *firstQVar1 =
      env.unqualifiedLookup_one(firstQ->qualifier, LF_QUALIFIER_LOOKUP);
    HANDLE_DEPENDENT(firstQVar1);
    if (firstQVar1 &&
        !firstQVar1->isNamespace() &&
        !firstQVar1->isClass()) {
      return env.error(firstQ->loc, stringc
        << "in " << this->asString() << ", when " << firstQ->qualifier
        << " is found in the current scope, it must be "
        << "a class or namespace, not " << kindAndType(firstQVar1));
    }
    Scope *firstQScope1 = (!firstQVar1)?             NULL :
                          firstQVar1->isNamespace()? firstQVar1->scope :
                                                     firstQVar1->type->asCompoundType();

    // lookup of firstQ in scope of LHS class
    Variable *firstQVar2 =
      ct->lookup_one(firstQ->qualifier, env, LF_QUALIFIER_LOOKUP);
    HANDLE_DEPENDENT(firstQVar2);
    if (firstQVar2 &&
        !firstQVar2->isClass()) {
      return env.error(firstQ->loc, stringc
        << "in " << this->asString() << ", when " << firstQ->qualifier
        << " is found in the class of " << obj->asString() << ", it must be "
        << "a class, not " << kindAndType(firstQVar2));
    }
    Scope *firstQScope2 = (!firstQVar2)? NULL :
                                         firstQVar2->type->asCompoundType();

    // combine the two lookups
    if (firstQScope1) {
      if (firstQScope2 && firstQScope1!=firstQScope2) {
        return env.error(firstQ->loc, stringc
          << "in " << this->asString() << ", " << firstQ->qualifier
          << " was found in the current scope as "
          << kindAndType(firstQVar1) << ", and also in the class of "
          << obj->asString() << " as "
          << kindAndType(firstQVar2) << ", but they must be the same");
      }
    }
    else {
      if (firstQScope2) {
        firstQScope1 = firstQScope2;     // make 'firstQScope1' the only one
      }
      else {
        return env.error(firstQ->loc, stringc
          << "no such scope `" << firstQ->qualifier << "'");
      }
    }

    // lookup the remainder of 'fieldName', but we already know
    // that 'firstQ' maps to 'firstQScope1'
    env.lookupPQ_withScope(candidates, firstQ->rest, flags, firstQScope1);
  }

  else {
    // unqualified field name: 3.4.5p1,2,3

    if (isDestructor) {
      // doc/lookup.txt case 2

      // unqualified lookup
      Variable *var1 = env.unqualifiedLookup_one(rhsFinalTypeName, flags);
      HANDLE_DEPENDENT(var1);
      if (var1 && !var1->isClass()) {
        return env.error(fieldName->loc, stringc
          << "in " << this->asString() << ", when " << rhsFinalTypeName
          << " is found in the current scope, it must be "
          << "a class, not " << kindAndType(var1));
      }

      // lookup in class of LHS
      Variable *var2 = ct->lookup_one(rhsFinalTypeName, env, flags);
      HANDLE_DEPENDENT(var2);
      if (var2 && !var2->isClass()) {
        return env.error(fieldName->loc, stringc
          << "in " << this->asString() << ", when " << rhsFinalTypeName
          << " is found in the class of " << obj->asString()
          << ", it must be a class, not " << kindAndType(var2));
      }

      // combine
      if (var1) {
        if (var2) {
          if (!sameCompounds(var1, var2)) {
            return env.error(fieldName->loc, stringc
              << "in " << this->asString() << ", " << rhsFinalTypeName
              << " was found in the current scope as "
              << kindAndType(var1) << ", and also in the class of "
              << obj->asString() << " as "
              << kindAndType(var2) << ", but they must be the same");
          }
          // we will use 'var2' below
        }
        else {
          // Use 'var2' the rest of the way.
          //
          // The reason to prefer 'var2' over 'var1' is a little
          // subtle.  Normally, they are the same so it does not
          // matter.  But in a case like in/t0481.cc, 'var2' is a
          // template instantiation, whereas 'var1' is just a template
          // primary.  So, use the more specific one.
          var2 = var1;
        }
      }
      else {
        if (var2) {
          // we will use 'var2', so nothing needs to be done
        }
        else {
          return env.error(fieldName->loc, stringc
            << "no such class `" << rhsFinalTypeName << "'");
        }
      }

      // get the destructor of the named class
      env.lookupClassDestructor(candidates, var2->type->asCompoundType(), flags);
        //             using 'var2' here    ^^^^
    }

    else {
      // doc/lookup.txt cases 1,2,4,5,6

      // lookup 'fieldName' in 'ct', taking any template arguments
      // or conversion function types into account
      env.unqualifiedFinalNameLookup(candidates, ct, fieldName, flags);
    }
  }
  
  #undef HANDLE_DEPENDENT
  
  // should only get members of 'ct' or base classes
  SFOREACH_OBJLIST(Variable, candidates, iter) {
    Variable const *v = iter.data();

    if (v->scope == ct) {
      continue;         // easy case
    }
    
    if (!v->scope || !v->scope->curCompound) {
      return env.error(fieldName->loc, stringc
        << "field `" << *fieldName << "' is not a class member");
    }

    CompoundType *vClass = v->scope->curCompound;
    int subobjs = ct->countBaseClassSubobjects(vClass);
    if (!subobjs) {
      return env.error(fieldName->loc, stringc
        << "field `" << *fieldName << "' is a member of "
        << kindAndType(vClass->typedefVar)
        << ", which is not a base class of "
        << kindAndType(ct->typedefVar));
    }

    // 10.2p2: must not ambiguously refer to fields of distinct
    // subobjects
    //
    // Scope::lookupVariable_considerBase has some overlapping
    // functionality.  It seems to me that the check here should
    // subsume the one in Scope, and furthermore I think *both*
    // implementations may have subtle bugs, but I can't figure out a
    // test that would properly reveal where the bugs/differences are
    // (this is just a confusing part of the spec).  So, for the
    // moment, the functionality remains duplicated.
    //
    // For example, I suspect that 'subobjs>1' is too crude because it
    // does not take into account the notion of "hiding" defined in
    // 10.2p2.
    if (!v->hasFlag(DF_STATIC) && subobjs>1) {
      return env.error(fieldName->loc, stringc
        << "field `" << *fieldName << "' ambiguously refers to "
        << "elements of multiple base class subobjects");
    }
  }

  // investigate what lookup yielded

  Variable *basef = NULL;
  if (!candidates.isEmpty()) {
    basef = candidates.first();

    // should not be a type (5.2.5p4b4)
    if (basef->hasFlag(DF_TYPEDEF))
      basef = NULL;
  }

  if (!basef) {
    TemplateInfo *ti = ct->templateInfo();
    if (ti && ti->dependentBases.isNotEmpty()) {
      // (in/t0502.cc) the member could be coming from a dependent
      // base; do not issue an error (but return ST_ERROR to prevent
      // the context from trying to do more)
      return env.errorType();
    }

    // bhackett: check to see if this is an access through anonymous fields.
    ArrayStack<Variable*> anon_fields;
    if (findAnonymousField(env, ct, fieldName, anon_fields)) {
      while (anon_fields.length() > 1) {
        Variable *outer_anon = anon_fields.pop();

        // get a new field access to the anonymous structure field.
        PQName *newField = new PQ_name(outer_anon->loc, outer_anon->name);
        E_fieldAcc *new_obj = new E_fieldAcc(obj, newField);

        // we can't tcheck it since the anonymous field is a struct/union
        // name and isn't in any scope, so fill in field and type directly.
        new_obj->field = outer_anon;
        new_obj->type =
          makeFieldLvalType(env, outer_anon, lhsType->getCVFlags());

        // replace our base expression with the explicit anon field access.
        obj = new_obj;
      }

      field = anon_fields[0];

      // copy of code below for non-anonymous case.
      if (obj->type->isLval()) {
        // TODO: this is wrong if the field names an enumerator (5.2.5p4b5)
        return makeFieldLvalType(env, field, lhsType->getCVFlags());
      }
      else {
        return field->type;
      }
    }

    return env.error(lhsType, stringc
      << "there is no member called `" << *fieldName
      << "' in " << lhsType->toString());
  }

  // nominal lookup result for remaining checks; if this name is
  // overloaded, this should get overwritten after overload resolution

  // TODO: access control check

  if (!(flags & LF_TEMPL_PRIMARY)) {
    env.ensureFuncBodyTChecked(basef);
  }
  field = env.storeVarIfNotOvl(basef);

  // type of expression is type of field; possibly as an lval
  if (obj->type->isLval()) {
    // TODO: this is wrong if the field names an enumerator (5.2.5p4b5)
    return makeFieldLvalType(env, field, lhsType->getCVFlags());
  }
  else {
    return field->type;
  }
}


Type *E_arrow::itcheck_x(Env &env, Expression *&replacement)
{
  LookupSet dummy;
  return itcheck_arrow_set(env, replacement, LF_NONE, dummy);
}

// Nominally, we rewrite
//   a->b                 E_arrow(a,b)
// as
//   (*a).b               E_fieldAcc(E_deref(a), b)
//
// However, 'a' might be an object with operator-> defined, in which
// case we rewrite the LHS, adding an explicit operator-> call:
//   (a.operator->()).b   E_fieldAcc(E_funCall(E_fieldAcc(a,operator->), ()), b)
//
// Further complicating this is the possibility that we are in a
// template, and don't know how much rewriting to do because of
// dependence on template parameters.
//
// So, every a->b in the input AST has one of three fates:
//   - If the type of 'a' does not depend on an template parameters,
//     and is a pointer type, it is changed into (*a).b.
//   - If 'a' is not dependent and has class type with operator->
//     defined, it is changed into (a.operator->())->b.
//   - If 'a' has dependent type, it is left as a->b, and only further
//     refined when the instantiation is typechecked.
//
// Note that the middle case, rewriting as operator->, yields a form
// that again contains -> and therefore may be recursively rewritten.
// The recursion stops in case 1 or 3.  (Incidentally, the code below
// does the expansion iteratively, not recursively.)
//
// Examples of various levels and timings of rewriting can be seen by
// running ccparse with the prettyPrint tracing flag on in/t0480.cc
Type *E_arrow::itcheck_arrow_set(Env &env, Expression *&replacement,
                                 LookupFlags flags, LookupSet &set)
{
  // check LHS
  obj->tcheck(env, obj);

  // overloaded?  if so, replace 'obj'
  Type *t = obj->type;
  while (t && !t->isDependent()) {
    t = resolveOverloadedUnaryOperator(env, obj, this, obj, OP_ARROW);
    // keep sticking in 'operator->' until the LHS is not a class
  }

  // now replace with '*' and '.' and proceed
  E_fieldAcc *eacc = new E_fieldAcc(new E_deref(obj), fieldName);
  if (t && t->isDependent()) {
    // Do not actually do the rewriting, since the degree to which
    // further rewriting via operator-> is done depends on template
    // parameters.  We still go ahead and create 'eacc' and use it to
    // compute the type of this node, though.  (in/t0478.cc)
  }
  else {
    replacement = eacc;
  }
  return eacc->itcheck_fieldAcc_set(env, flags, set);
}


Type *E_sizeof::itcheck_x(Env &env, Expression *&replacement)
{
  expr->tcheck(env, expr);

  return env.sizeofType(expr->type, size, expr);
}


// do operator overload resolution for a unary operator; return
// non-NULL if we've replaced this node, and want the caller to
// return that value
Type *resolveOverloadedUnaryOperator(
  Env &env,                  // environment
  Expression *&replacement,  // OUT: replacement node
  Expression *ths,           // expression node that is being resolved (not used)
  Expression *expr,          // the subexpression of 'this' (already type-checked)
  OverloadableOp op          // which operator this node is
) {
  // 14.6.2.2 para 1
  if (expr->type->containsGeneralizedDependent()) {
    return env.dependentType();
  }

  if (!env.doOperatorOverload()) {
    return NULL;
  }

  if (expr->type->asRval()->isCompoundType() ||
      expr->type->asRval()->isEnumType()) {
    OVERLOADINDTRACE("found overloadable unary " << toString(op) <<
                     " near " << env.locStr());
    StringRef opName = env.operatorName[op];

    // argument information
    ArgumentInfoArray args(1);
    getArgumentInfo(env, args[0], expr);

    // prepare resolver
    OverloadResolver resolver(env, env.loc(), &env.errors,
                              OF_OPERATOR,
                              NULL, // I assume operators can't have explicit template arguments
                              args);

    if (op == OP_AMPERSAND) {
      // 13.3.1.2 para 9: no viable -> use built-in
      resolver.emptyCandidatesIsOk = true;
    }

    // user-defined candidates
    resolver.addUserOperatorCandidates(expr->type, NULL /*rhsType*/, opName);

    // built-in candidates
    resolver.addBuiltinUnaryCandidates(op);

    // pick the best candidate
    bool dummy;
    Candidate const *winnerCand = resolver.resolveCandidate(dummy);
    if (winnerCand) {
      Variable *winner = winnerCand->var;

      if (!winner->hasFlag(DF_BUILTIN)) {
        OperatorName *oname = new ON_operator(op);
        PQ_operator *pqo = new PQ_operator(SL_UNKNOWN, oname, opName);

        if (winner->hasFlag(DF_MEMBER)) {
          // replace '~a' with 'a.operator~()'
          replacement = new E_funCall(
            new E_fieldAcc(expr, pqo),               // function
            FakeList<ArgExpression>::emptyList()     // arguments
          );
          replacement->replaceExpr = ths;
        }
        else {
          // replace '~a' with '<scope>::operator~(a)'
          replacement = new E_funCall(
            // function to invoke
            new E_variable(env.makeFullyQualifiedName(winner->scope, pqo)),
            // arguments
            makeExprList1(expr)
          );
          replacement->replaceExpr = ths;
        }

        // for now, just re-check the whole thing
        replacement->tcheck(env, replacement);
        return replacement->type;
      }

      else {
        // chose a built-in operator

        // TODO: need to replace the arguments according to their
        // conversions (if any)

        // get the correct return value, at least
        Type *ret = resolver.getReturnType(winnerCand);
        OVERLOADINDTRACE("computed built-in operator return type `" <<
                         ret->toString() << "'");

        return ret;
      }
    }
  }

  // not replaced
  return NULL;
}


// similar, but for binary
Type *resolveOverloadedBinaryOperator(
  Env &env,                  // environment
  Expression *&replacement,  // OUT: replacement node
  Expression *ths,           // expression node that is being resolved (not used)
  Expression *e1,            // left subexpression of 'this' (already type-checked)
  Expression *e2,            // right subexpression, or NULL for postfix inc/dec
  OverloadableOp op,         // which operator this node is
  ArgumentInfoArray &argInfo // carries info about overloaded func arg names
) {
  // 14.6.2.2 para 1
  if (e1->type->containsGeneralizedDependent() ||
      e2 && e2->type->containsGeneralizedDependent()) {
    return env.dependentType();
  }

  if (!env.doOperatorOverload()) {
    return NULL;
  }

  // check for operator overloading
  if (e1->type->asRval()->isCompoundType() ||
      e1->type->asRval()->isEnumType() ||
      e2 && e2->type->asRval()->isCompoundType() ||
      e2 && e2->type->asRval()->isEnumType()) {
    OVERLOADINDTRACE("found overloadable binary " << toString(op) <<
                     " near " << env.locStr());
    StringRef opName = env.operatorName[op];

    // for postfix inc/dec, the second parameter is 'int'
    if (!e2) {
      argInfo[1] = ArgumentInfo(SE_NONE, env.getSimpleType(ST_INT));
    }

    // prepare the overload resolver
    OverloadResolver resolver(env, env.loc(), &env.errors,
                              OF_OPERATOR,
                              NULL, // I assume operators can't have explicit template arguments
                              argInfo, 10 /*numCand*/);
    if (op == OP_COMMA) {
      // 13.3.1.2 para 9: no viable -> use built-in
      resolver.emptyCandidatesIsOk = true;
    }

    // user-defined candidates
    resolver.addUserOperatorCandidates(argInfo[0].type, argInfo[1].type, opName);

    // built-in candidates
    resolver.addBuiltinBinaryCandidates(op, argInfo[0], argInfo[1]);

    // pick one
    bool dummy;
    Candidate const *winnerCand = resolver.resolveCandidate(dummy);
    if (winnerCand) {
      Variable *winner = winnerCand->var;
      FunctionType *winnerFt = winner->type->asFunctionType();

      if (!e2) {
        // synthesize and tcheck a 0 for the second argument to postfix inc/dec
        e2 = new E_intLit(env.str("0"));
        e2->tcheck(env, e2);
      }

      env.possiblySetOverloadedFunctionVar(e1, winnerFt->params.nth(0)->type,
                                           argInfo[0].overloadSet);
      env.possiblySetOverloadedFunctionVar(e2, winnerFt->params.nth(1)->type,
                                           argInfo[1].overloadSet);

      if (!winner->hasFlag(DF_BUILTIN)) {
        PQ_operator *pqo = new PQ_operator(SL_UNKNOWN, new ON_operator(op), opName);
        if (winner->hasFlag(DF_MEMBER)) {
          // replace 'a+b' with 'a.operator+(b)'
          replacement = new E_funCall(
            // function to invoke
            new E_fieldAcc(e1, pqo),
            // arguments
            makeExprList1(e2)
          );
          replacement->replaceExpr = ths;
        }
        else {
          // replace 'a+b' with '<scope>::operator+(a,b)'
          replacement = new E_funCall(
            // function to invoke
            new E_variable(env.makeFullyQualifiedName(winner->scope, pqo)),
            // arguments
            makeExprList2(e1, e2)
          );
          replacement->replaceExpr = ths;
        }

        // for now, just re-check the whole thing
        replacement->tcheck(env, replacement);
        return replacement->type;
      }

      else {
        // chose a built-in operator

        // TODO: need to replace the arguments according to their
        // conversions (if any)

        if (op == OP_BRACKETS) {
          // built-in a[b] is equivalent to *(a+b)
          //
          // 2005-08-09 (in/t0530.cc): but we *cannot* do a recursive
          // tcheck, because the '*' and '+' are not subject to
          // overload resolution; so, compute types manually
          //
          // Note that this has the effect of making tcheck+prettyPrint
          // not idempotent, since the output expression *(a+b) will
          // be subject to overload resolution and therefore can mean
          // something different ...

          Type *ret = resolver.getReturnType(winnerCand);

          E_binary *bin = new E_binary(e1, BIN_PLUS, e2);
          bin->type = env.tfac.makePointerType(CV_NONE, ret->asRval());

          E_deref *deref = new E_deref(bin);
          deref->type = ret;

          replacement = deref;
          return deref->type;
        }
        else {
          // get the correct return value, at least
          Type *ret = resolver.getReturnType(winnerCand);
          OVERLOADINDTRACE("computed built-in operator return type `" <<
                           ret->toString() << "'");
          return ret;
        }
      }
    }
  }

  // not replaced
  return NULL;
}


bool isArithmeticOrEnumType(Type *t)
{
  if (t->isSimpleType()) {
    return isArithmeticType(t->asSimpleTypeC()->type);
  }
  return t->isEnumType();
}


Type *E_unary::itcheck_x(Env &env, Expression *&replacement)
{
  expr->tcheck(env, expr);

  // consider the possibility of operator overloading
  Type *ovlRet = resolveOverloadedUnaryOperator(
    env, replacement, this, expr, toOverloadableOp(op));
  if (ovlRet) {
    this->type = ovlRet;
    return ovlRet;
  }

  Type *t = expr->type->asRval();

  // make sure 'expr' is compatible with given operator
  switch (op) {
    default:
      xfailure("bad operator kind");

    case UNY_PLUS:
      // 5.3.1 para 6
      if (isArithmeticOrEnumType(t)) {
        return env.getSimpleType(applyIntegralPromotions(t));
      }
      if (t->isPointerType()) {
        return t;
      }
      return env.error(t, stringc
        << "argument to unary + must be of arithmetic, enumeration, or pointer type, not `"
        << t->toString() << "'");

    case UNY_MINUS:
      // 5.3.1 para 7
      if (isArithmeticOrEnumType(t)) {
        return env.getSimpleType(applyIntegralPromotions(t));
      }
      return env.error(t, stringc
        << "argument to unary - must be of arithmetic or enumeration type, not `"
        << t->toString() << "'");

    case UNY_NOT: {
      // 5.3.1 para 8
      Type *t_bool = env.getSimpleType(ST_BOOL);
      if (!getImplicitConversion(env, expr->getSpecial(env.lang), t, t_bool)) {
        env.error(t, stringc
          << "argument to unary ! must be convertible to bool; `"
          << t->toString() << "' is not");
      }
      return t_bool;
    }

    case UNY_BITNOT:
      // 5.3.1 para 9
      if (t->isIntegerType() || t->isEnumType()) {
        return env.getSimpleType(applyIntegralPromotions(t));
      }
      return env.error(t, stringc
        << "argument to unary ~ must be of integer or enumeration type, not `"
        << t->toString() << "'");
        
      // 5.3.1 para 9 also mentions an ambiguity with "~X()", which I
      // tried to exercise in in/t0343.cc, but I can't seem to get it;
      // so either Elsa already does what is necessary, or I do not
      // understand the syntax adequately ....
  }
}


Type *E_effect::itcheck_x(Env &env, Expression *&replacement)
{
  ArgumentInfoArray argInfo(2);
  tcheckArgumentExpression(env, expr, argInfo[0]);
  
  if (argInfo[0].overloadSet.isNotEmpty()) {
    env.error(stringc << "cannot use overloaded function name with " << toString(op));
  }

  // consider the possibility of operator overloading
  Type *ovlRet = isPrefix(op)?
    resolveOverloadedUnaryOperator(
      env, replacement, this, expr, toOverloadableOp(op)) :
    resolveOverloadedBinaryOperator(
      env, replacement, this, expr, NULL, toOverloadableOp(op), argInfo) ;
  if (ovlRet) {
    this->type = ovlRet;
    return ovlRet;
  }

  // TODO: make sure 'expr' is compatible with given operator

  // dsw: FIX: check that the argument is an lvalue.

  // Cppstd 5.2.6 "Increment and decrement: The value obtained by
  // applying a postfix ++ ... .  The result is an rvalue."; Cppstd
  // 5.3.2 "Increment and decrement: The operand of prefix ++ ... .
  // The value ... is an lvalue."
  Type *ret = expr->type->asRval();
  if (op == EFF_PREINC || op == EFF_PREDEC) {
    ret = env.makeReferenceType(ret);
  }
  return ret;
}


bool isComplexOrImaginary(Type *t)
{       
  t = t->asRval();
  return t->isSimpleType() &&
         isComplexOrImaginary(t->asSimpleTypeC()->type);
}

Type *E_binary::itcheck_x(Env &env, Expression *&replacement)
{
  ArgumentInfoArray argInfo(2);
  tcheckArgumentExpression(env, e1, argInfo[0]);
  tcheckArgumentExpression(env, e2, argInfo[1]);

  // help disambiguate t0182.cc
  if (op == BIN_LESS && e1->type->isFunctionType()) {
    // For C++, this rule is implied by 5.9, which does not permit
    // conversions for function-typed operands.
    //
    // For C, this is implied by 6.5.8, which not only fails to
    // provide conversions for function-typed operands, but doesn't
    // even allow relational comparison of pointer-to-function-typed
    // operands!  Of course, the latter is a ubiquitous extension so
    // I will continue to allow it.
    //
    // Note that both GCC and ICC allow this.  However, I have only
    // seen it happen in real code twice, and *both* times the real
    // code actually contained a bug (the programmer intended to
    // *call* the function, not compare its address), so I do not
    // intend to replicate their bugs in this case.
    // (in/gnu/bugs/gb0003.cc)
    return env.error("cannot apply '<' to a function; instead, call it "
                     "or explicitly take its address", EF_DISAMBIGUATES);
  }

  // gnu/c99 complex arithmetic?
  #ifdef GNU_EXTENSION
    if (isComplexOrImaginary(e1->type) || isComplexOrImaginary(e2->type)) {
      return itcheck_complex_arith(env);
    }
  #endif // GNU_EXTENSION

  // check for operator overloading
  if (isOverloadable(op)) {
    Type *ovlRet = resolveOverloadedBinaryOperator(
      env, replacement, this, e1, e2, toOverloadableOp(op), argInfo);
    if (ovlRet) {
      this->type = ovlRet;
      return ovlRet;
    }
  }

  // TODO: much of what follows is obviated by the fact that
  // 'resolveOverloadedBinaryOperator' now returns non-NULL for
  // built-in operator candidates ...

  if (op == BIN_BRACKETS) {
    // built-in a[b] is equivalent to *(a+b)
    replacement = new E_deref(new E_binary(e1, BIN_PLUS, e2));
    replacement->tcheck(env, replacement);
    return replacement->type;
  }

  // get types of arguments, converted to rval, and normalized with
  // array-to-pointer and function-to-pointer conversions
  Type *lhsType = env.operandRval(e1->type);
  Type *rhsType = env.operandRval(e2->type);

  switch (op) {
    default: xfailure("illegal op code"); break;

    case BIN_EQUAL:               // ==
    case BIN_NOTEQUAL:            // !=
    case BIN_LESS:                // <
    case BIN_GREATER:             // >
    case BIN_LESSEQ:              // <=
    case BIN_GREATEREQ:           // >=

    case BIN_AND:                 // &&
    case BIN_OR:                  // ||
    case BIN_IMPLIES:             // ==>
    case BIN_EQUIVALENT:          // <==>
      return env.getSimpleType(ST_BOOL);

    case BIN_COMMA:
      // dsw: I changed this to allow the following: &(3, a);
      return e2->type/*rhsType*/;

    case BIN_PLUS:                // +
      // case: p + n
      if (lhsType->isPointerType()) {
        return lhsType;
      }

      // case: n + p
      if (lhsType->isIntegerType() && rhsType->isPointerType()) {
        return rhsType;         // a pointer type, that is
      }

      return usualArithmeticConversions(env.tfac, lhsType, rhsType);

    case BIN_MINUS:               // -
      // case: p - p
      if (lhsType->isPointerType() && rhsType->isPointerType() ) {
        return env.getSimpleType(ST_INT);
      }

      // case: p - n
      if (lhsType->isPointerType()) {
        return lhsType;
      }

      return usualArithmeticConversions(env.tfac, lhsType, rhsType);

    case BIN_MULT:                // *
    case BIN_DIV:                 // /
    case BIN_MOD:                 // %
      // in/t0533.cc
      return usualArithmeticConversions(env.tfac, lhsType, rhsType);

    case BIN_LSHIFT:              // <<
    case BIN_RSHIFT:              // >>
    case BIN_BITAND:              // &
    case BIN_BITXOR:              // ^
    case BIN_BITOR:               // |
    case BIN_MINIMUM:             // <?
    case BIN_MAXIMUM:             // >?
      // default behavior of returning the left side is close enough for now.
      break;

    // BIN_ASSIGN can't appear in E_binary

    case BIN_DOT_STAR:            // .*
    case BIN_ARROW_STAR:          // ->*
      // [cppstd 5.5]
      if (op == BIN_ARROW_STAR) {
        // left side should be a pointer to a class
        if (!lhsType->isPointer()) {
          return env.error(stringc
            << "left side of ->* must be a pointer, not `"
            << lhsType->toString() << "'");
        }
        lhsType = lhsType->asPointerType()->atType;
      }

      if (lhsType->isGeneralizedDependent()) {
        return env.dependentType();    // in/k0001.cc
      }

      // left side should be a class
      CompoundType *lhsClass = lhsType->ifCompoundType();
      if (!lhsClass) {
        return env.error(op==BIN_DOT_STAR?
          "left side of .* must be a class or reference to a class" :
          "left side of ->* must be a pointer to a class");
      }

      // right side should be a pointer to a member
      if (!rhsType->isPointerToMemberType()) {
        return env.error("right side of .* or ->* must be a pointer-to-member");
      }
      PointerToMemberType *ptm = rhsType->asPointerToMemberType();

      // actual LHS class must be 'ptm->inClass()', or a
      // class unambiguously derived from it
      int subobjs = lhsClass->countBaseClassSubobjects(ptm->inClass());
      if (subobjs == 0) {
        return env.error(stringc
          << "the left side of .* or ->* has type `" << lhsClass->name
          << "', but this is not equal to or derived from `" << ptm->inClass()->name
          << "', the class whose members the right side can point at");
      }
      else if (subobjs > 1) {
        return env.error(stringc
          << "the left side of .* or ->* has type `" << lhsClass->name
          << "', but this is derived from `" << ptm->inClass()->name
          << "' ambiguously (in more than one way)");
      }

      // the return type is essentially the 'atType' of 'ptm'
      Type *ret = ptm->atType;

      // 8.3.3 para 3: "A pointer to member shall not point to ... a
      // member with reference type."  Scott says this can't happen
      // here.
      xassert(!ret->isReference());

      // [cppstd 5.5 para 6]
      // but it might be an lvalue if it is a pointer to a data
      // member, and either
      //   - op==BIN_ARROW_STAR, or
      //   - op==BIN_DOT_STAR and 'e1->type' is an lvalue
      if (op==BIN_ARROW_STAR ||
          /*must be DOT_STAR*/ e1->type->isLval()) {
        // this internally handles 'ret' being a function type
        ret = makeLvalType(env, ret);
      }

      return ret;
  }

  // TODO: make sure 'expr' is compatible with given operator

  return lhsType;
}


// someone took the address of 'var', and we must compute
// the PointerToMemberType of that construct
static Type *makePTMType(Env &env, Variable *var, SourceLoc loc)
{
  // cppstd: 8.3.3 para 3, can't be static
  xassert(!var->hasFlag(DF_STATIC));
  
  // this is essentially a consequence of not being static
  if (var->type->isFunctionType()) {
    xassert(var->type->asFunctionType()->isMethod());
  }

  // cppstd: 8.3.3 para 3, can't be cv void
  if (var->type->isVoid()) {
    return env.error(loc, "attempted to make a pointer to member to void");
  }
  // cppstd: 8.3.3 para 3, can't be a reference
  if (var->type->isReference()) {
    return env.error(loc, "attempted to make a pointer to member to a reference");
  }

  CompoundType *inClass0 = var->scope->curCompound;
  xassert(inClass0);

  return env.tfac.makePointerToMemberType
    (inClass0, CV_NONE, var->type);
}

Type *E_addrOf::itcheck_x(Env &env, Expression *&replacement)
{
  LookupSet dummy;
  return itcheck_addrOf_set(env, replacement, LF_NONE, dummy);
}

Type *E_addrOf::itcheck_addrOf_set(Env &env, Expression *&replacement,
                                   LookupFlags flags, LookupSet &set)
{
  // might we be forming a pointer-to-member?
  bool possiblePTM = false;
  E_variable *evar = NULL;
  // NOTE: do *not* unwrap any layers of parens:
  // cppstd 5.3.1 para 3: "A pointer to member is only formed when
  // an explicit & is used and its operand is a qualified-id not
  // enclosed in parentheses."
  if (expr->isE_variable()) {
    evar = expr->asE_variable();

    // cppstd 5.3.1 para 3: Nor is &unqualified-id a pointer to
    // member, even within the scope of the unqualified-id's
    // class.
    // dsw: Consider the following situation: How do you know you
    // &x isn't making a pointer to member?  Only because the name
    // isn't fully qualified.
    //   struct A {
    //     int x;
    //     void f() {int *y = &x;}
    //   };
    if (evar->name->hasQualifiers()) {
      possiblePTM = true;

      // suppress elaboration of 'this'; the situation where 'this'
      // would be inserted is exactly the situation where a
      // pointer-to-member is formed
      flags |= LF_NO_IMPL_THIS;
    }
  }

  // check 'expr'
  tcheckExpression_set(env, expr/*INOUT*/, flags, set);

  if (expr->type->isError()) {
    // skip further checking because the tree is not necessarily
    // as the later stages expect; e.g., an E_variable might have
    // a NULL 'var' field
    return expr->type;
  }

  // 14.6.2.2 para 1
  if (expr->type->containsGeneralizedDependent()) {
    return env.dependentType();
  }

  if (possiblePTM) {
    // TODO: If the variable was the name of an overloaded function,
    // then we will have not yet done resolution of the name, and
    // consequently 'evar->var' may not be the correct function.

    // make sure we instantiate any functions that have their address
    // taken
    xassert(evar->var);
    env.ensureFuncBodyTChecked(evar->var);

    if (evar->var->isMember() &&
        !evar->var->isStatic()) {
      return makePTMType(env, evar->var, evar->name->loc);
    }
  }

  // ok to take addr of function; special-case it so as not to weaken
  // what 'isLval' means
  if (expr->type->isFunctionType()) {
    return env.makePtrType(expr->type);
  }

  // consider the possibility of operator overloading
  Type *ovlRet = resolveOverloadedUnaryOperator(
    env, replacement, this, expr, OP_AMPERSAND);
  if (ovlRet) {
    this->type = ovlRet;
    return ovlRet;
  }

  if (!expr->type->isLval()) {
    return env.error(expr->type, stringc
      << "cannot take address of non-lvalue `" 
      << expr->type->toString() << "'");
  }
  ReferenceType *rt = expr->type->asReferenceType();

  // change the "&" into a "*"
  return env.makePtrType(rt->atType);
}


Type *E_deref::itcheck_x(Env &env, Expression *&replacement)
{
  ptr->tcheck(env, ptr);

  // check for overloading
  {
    Type *ovlRet = resolveOverloadedUnaryOperator(
      env, replacement, this, ptr, OP_STAR);
    if (ovlRet) {
      this->type = ovlRet;
      return ovlRet;
    }
  }

  // clone the type as it's taken out of one AST node, so it
  // can then be used as the type of another AST node (this one)
  Type *rt = ptr->type->asRval();

  if (rt->isFunctionType()) {
    return rt;                         // deref is idempotent on FunctionType-s
  }

  if (rt->isPointerType()) {
    PointerType *pt = rt->asPointerType();

    // dereferencing yields an lvalue
    return makeLvalType(env, pt->atType);
  }

  // implicit coercion of array to pointer for dereferencing
  if (rt->isArrayType()) {
    return makeLvalType(env, rt->asArrayType()->eltType);
  }

  return env.error(rt, stringc
    << "cannot dereference non-pointer type `" << rt->toString() << "'");
}


// This returns true if 'atype' is defining a type.  However,
// this function is only called in C++ mode, because in C mode
// it is legal to define a type in a cast.
bool hasTypeDefn(ASTTypeId *atype)
{
  return atype->spec->isTS_classSpec() ||
         atype->spec->isTS_enumSpec();
}

Type *E_cast::itcheck_x(Env &env, Expression *&replacement)
{
  // check the dest type
  if (hasTypeDefn(ctype)) {
    if (env.lang.isCplusplus) {
      // 5.4p3: not allowed
      return env.error(ctype->spec->loc, "cannot define types in a cast");
    }
    else {
      // similar to the E_sizeofType case
      if (!tcheckedType) {
        InstantiationContextIsolator isolate(env, env.loc());
        tcheckedType = true;

        ASTTypeId::Tcheck tc(DF_NONE, DC_E_CAST);
        ctype = ctype->tcheck(env, tc);
      }
    }
  }

  else {
    // usual behavior
    ASTTypeId::Tcheck tc(DF_NONE, DC_E_CAST);
    ctype = ctype->tcheck(env, tc);
  }

  // check the source expression
  expr->tcheck(env, expr);
  
  // TODO: check that the cast makes sense

  Type *ret = ctype->getType();

  // This is a gnu extension: in C mode, if the expr is an lvalue,
  // make the returned type an lvalue.  This is in direct
  // contradiction to the C99 spec: Section 6.5.4, footnote 85: "A
  // cast does not yield an lvalue".
  // http://gcc.gnu.org/onlinedocs/gcc-3.1/gcc/Lvalues.html
  if (env.lang.lvalueFlowsThroughCast) {
    if (expr->getType()->isReference() && !ret->isReference()) {
      ret = env.makeReferenceType(ret);
    }
  }

  return ret;
}


// try to convert t1 to t2 as per the rules in 5.16 para 3; return
// NULL if conversion is not possible, otherwise return type to which
// 't1' is converted (it is not always exactly 't2') and set 'ic'
// accordingly
Type *attemptCondConversion(Env &env, ImplicitConversion &ic /*OUT*/,
                            Type *t1, Type *t2)
{
  // bullet 1: attempt direct conversion to lvalue
  if (t2->isLval()) {
    ic = getImplicitConversion(env, SE_NONE, t1, t2);
    if (ic) {
      return t2;
    }
  }

  // bullet 2
  CompoundType *t1Class = t1->asRval()->ifCompoundType();
  CompoundType *t2Class = t2->asRval()->ifCompoundType();
  if (t1Class && t2Class &&
      (t1Class->hasBaseClass(t2Class) ||
       t2Class->hasBaseClass(t1Class))) {
    // bullet 2.1
    if (t1Class->hasBaseClass(t2Class) &&
        t2->asRval()->getCVFlags() >= t1->asRval()->getCVFlags()) {
      ic.addStdConv(SC_IDENTITY);
      return t2->asRval();
    }
    else {
      return NULL;
    }
  }
  else {
    // bullet 2.2
    t2 = t2->asRval();
    ic = getImplicitConversion(env, SE_NONE, t1, t2);
    if (ic) {
      return t2;
    }
  }

  return NULL;
}


// "array-to-pointer (4.2) and function-to-pointer (4.3) standard
// conversions"; (for the moment) functionally identical to
// 'normalizeParameterType' but specified by a different part of
// cppstd...
Type *arrAndFuncToPtr(Env &env, Type *t)
{
  if (t->isArrayType()) {
    return env.makePtrType(t->asArrayType()->eltType);
  }
  if (t->isFunctionType()) {
    return env.makePtrType(t);
  }
  return t;
}


// cppstd 5.9 "composite pointer type" computation
Type *compositePointerType
  (Env &env, PointerType *t1, PointerType *t2)
{
  // if either is pointer to void, result is void
  if (t1->atType->isVoid() || t2->atType->isVoid()) {
    CVFlags cv = t1->atType->getCVFlags() | t2->atType->getCVFlags();

    // reuse t1 or t2 if possible
    if (t1->atType->isVoid() && cv == t1->atType->getCVFlags()) {
      return t1;
    }
    if (t2->atType->isVoid() && cv == t2->atType->getCVFlags()) {
      return t2;
    }

    return env.tfac.makePointerType(CV_NONE,
      env.tfac.getSimpleType(ST_VOID, cv));
  }

  // types must be similar... aw hell.  I don't understand what the
  // standard wants, and my limited understanding is at odds with
  // what both gcc and icc do so.... hammer time
  bool whatev;
  return computeLUB(env, t1, t2, whatev);
}

// cppstd 5.16 computation similar to composite pointer but
// for pointer-to-member
Type *compositePointerToMemberType
  (Env &env, PointerToMemberType *t1, PointerToMemberType *t2)
{
  // hammer time
  bool whatev;
  return computeLUB(env, t1, t2, whatev);
}


// cppstd 5.16
Type *E_cond::itcheck_x(Env &env, Expression *&replacement)
{
  cond->tcheck(env, cond);

  // para 1: 'cond' converted to bool
  if (!getImplicitConversion(env, cond->getSpecial(env.lang), cond->type,
                             env.getSimpleType(ST_BOOL))) {
    env.error(cond->type, stringc
      << "cannot convert `" << cond->type->toString() 
      << "' to bool for conditional of ?:");
  }
  // TODO (elaboration): rewrite AST if a user-defined conversion was used

  th->tcheck(env, th);
  el->tcheck(env, el);

  // 14.6.2.2 para 1
  //
  // Note that I'm interpreting 14.6.2.2 literally, to the point of
  // regarding the entire ?: dependent if the condition is, even
  // though the type of the condition cannot affect the type of the ?:
  // expression.
  if (cond->type->containsGeneralizedDependent() ||
      th->type->containsGeneralizedDependent() ||
      el->type->containsGeneralizedDependent()) {
    return env.dependentType();
  }

  // pull out the types; during the processing below, we might change
  // these to implement "converted operand used in place of ..."
  Type *thType = th->type;
  Type *elType = el->type;

  Type *thRval = th->type->asRval();
  Type *elRval = el->type->asRval();

  if (!env.lang.isCplusplus) {
    // ANSI C99 mostly requires that the types be the same, but gcc
    // doesn't seem to enforce anything, so I won't either; and if
    // they are different, it isn't clear what the type should be ...

    bool bothLvals = thType->isLval() && elType->isLval();

    // for in/gnu/d0095.c
    if (thRval->isPointerType() &&
        thRval->asPointerType()->atType->isVoid()) {
      return bothLvals? elType : elRval;
    }
    
    // for in/c/t0025.c
    if (elRval->isPointerType() &&
        thRval->isIntegerType()) {
      return bothLvals? elType : elRval;
    }

    return bothLvals? thType : thRval;
  }

  // para 2: if one or the other has type 'void'
  {
    bool thVoid = thRval->isSimple(ST_VOID);
    bool elVoid = elRval->isSimple(ST_VOID);
    if (thVoid || elVoid) {
      if (thVoid && elVoid) {
        return thRval;         // result has type 'void'
      }

      // the void-typed expression must be a 'throw' (can it be
      // parenthesized?  a strict reading of the standard would say
      // no..), and the whole ?: has the non-void type
      if (thVoid) {
        if (!th->isE_throw()) {
          env.error("void-typed expression in ?: must be a throw-expression");
        }
        return arrAndFuncToPtr(env, elRval);
      }
      if (elVoid) {
        if (!el->isE_throw()) {
          env.error("void-typed expression in ?: must be a throw-expression");
        }
        return arrAndFuncToPtr(env, thRval);
      }
    }
  }

  // para 3: different types but at least one is a class type
  if (!thRval->equals(elRval) &&
      (thRval->isCompoundType() ||
       elRval->isCompoundType())) {
    // try to convert each to the other
    ImplicitConversion ic_thToEl;
    Type *thConv = attemptCondConversion(env, ic_thToEl, thType, elType);
    ImplicitConversion ic_elToTh;
    Type *elConv = attemptCondConversion(env, ic_elToTh, elType, thType);

    if (thConv && elConv) {
      return env.error("class-valued argument(s) to ?: are ambiguously inter-convertible");
    }

    if (thConv) {
      if (ic_thToEl.isAmbiguous()) {
        return env.error("in ?:, conversion of second arg to type of third is ambiguous");
      }

      // TODO (elaboration): rewrite AST according to 'ic_thToEl'
      thType = thConv;
      thRval = thType->asRval();
    }

    if (elConv) {
      if (ic_elToTh.isAmbiguous()) {
        return env.error("in ?:, conversion of third arg to type of second is ambiguous");
      }

      // TODO (elaboration): rewrite AST according to 'ic_elToTh'
      elType = elConv;
      elRval = elType->asRval();
    }
  }

  // para 4: same-type lval -> result is that type
  if (thType->isLval() &&
      elType->isLval() &&
      thType->equals(elType)) {
    return thType;
  }

  // para 5: overload resolution
  if (!thRval->equals(elRval) &&
      (thRval->isCompoundType() || elRval->isCompoundType())) {
    // collect argument info
    ArgumentInfoArray args(2);
    args[0].special = th->getSpecial(env.lang);
    args[0].type = thType;
    args[1].special = el->getSpecial(env.lang);
    args[1].type = elType;

    // prepare the overload resolver
    OverloadResolver resolver(env, env.loc(), &env.errors,
                              OF_NONE,
                              NULL, // no template arguments
                              args, 2 /*numCand*/);

    // built-in candidates
    resolver.addBuiltinBinaryCandidates(OP_QUESTION, args[0], args[1]);

    // pick one
    bool dummy;
    Candidate const *winnerCand = resolver.resolveCandidate(dummy);
    if (winnerCand) {
      Variable *winner = winnerCand->var;
      xassert(winner->hasFlag(DF_BUILTIN));

      // TODO (elaboration): need to replace the arguments according
      // to their conversions (if any)

      // get the correct return value, at least
      Type *ret = resolver.getReturnType(winnerCand);
      OVERLOADINDTRACE("computed built-in operator return type `" <<
                       ret->toString() << "'");

      // para 5 ends by saying (in effect) that 'ret' should be used
      // as the new 'thType' and 'elType' and then keep going on to
      // para 6; but I can't see how that would be different from just
      // returning here...
      return ret;
    }
  }
  
  // para 6: final standard conversions (conversion to rvalues has
  // already been done, so use the '*Rval' variables)
  {
    thRval = arrAndFuncToPtr(env, thRval);
    elRval = arrAndFuncToPtr(env, elRval);
    
    // bullet 1
    if (thRval->equals(elRval, MF_IGNORE_TOP_CV /*(in/t0499.cc)*/)) {
      return thRval;
    }
    
    // bullet 2
    if (isArithmeticOrEnumType(thRval) &&
        isArithmeticOrEnumType(elRval)) {
      return usualArithmeticConversions(env.tfac, thRval, elRval);
    }

    // bullet 3
    if (thRval->isPointerType() && el->getSpecial(env.lang) == SE_ZERO) {
      return thRval;
    }
    if (elRval->isPointerType() && th->getSpecial(env.lang) == SE_ZERO) {
      return elRval;
    }
    if (thRval->isPointerType() && elRval->isPointerType()) {
      Type *ret = compositePointerType(env,
        thRval->asPointerType(), elRval->asPointerType());
      if (!ret) { goto incompatible; }
      return ret;
    }

    // bullet 4
    if (thRval->isPointerToMemberType() && el->getSpecial(env.lang) == SE_ZERO) {
      return thRval;
    }
    if (elRval->isPointerToMemberType() && th->getSpecial(env.lang) == SE_ZERO) {
      return elRval;
    }
    if (thRval->isPointerToMemberType() && elRval->isPointerToMemberType()) {
      Type *ret = compositePointerToMemberType(env,
        thRval->asPointerToMemberType(), elRval->asPointerToMemberType());
      if (!ret) { goto incompatible; }
      return ret;
    }
  }

incompatible:
  return env.error(stringc
    << "incompatible ?: argument types `" << thRval->toString()
    << "' and `" << elRval->toString() << "'");
}

// bhackett
static Expression* GetArraySize(IDeclarator *idecl)
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

Type *E_sizeofType::itcheck_x(Env &env, Expression *&replacement)
{
  if (hasTypeDefn(atype)) {
    if (env.lang.isCplusplus) {
      // 5.3.3p5: cannot define types in 'sizeof'; the reason Elsa
      // enforces this rule is that if we allow type definitions then
      // there can be bad interactions with disambiguation (in/k0035.cc)
      return env.error(atype->spec->loc,
                       "cannot define types in a 'sizeof' expression");
    }
    else {
      // In C mode, it is legal to define types in a 'sizeof'; but
      // there are far fewer things that can go wrong during
      // disambiguation, so use a simple idempotency trick
      // (in/c/dC0019.c)
      if (!tchecked) {
        InstantiationContextIsolator isolate(env, env.loc());
        tchecked = true;

        ASTTypeId::Tcheck tc(DF_NONE, DC_E_SIZEOFTYPE);
        atype = atype->tcheck(env, tc);
      }
    }
  }

  else {
    // usual behavior
    ASTTypeId::Tcheck tc(DF_NONE, DC_E_SIZEOFTYPE);
    atype = atype->tcheck(env, tc);
  }


  // bhackett: watch for using sizeof on dynamically sized arrays.
  // convert these into multiplication expressions, e.g.
  // sizeof(int[x]) => sizeof(int) * x
  Type *mtype = atype->getType();

  if (mtype->isArrayType()) {
    ArrayType *ntype = mtype->asArrayType();

    if (ntype->size == ArrayType::DYN_SIZE) {
      Expression *size_exp = GetArraySize(atype->decl->decl);
      if (size_exp) {
        int inner_width;
        env.sizeofType(ntype->eltType, inner_width, NULL);

        char buf[100];
        sprintf(buf, "%d", inner_width);
        StringRef width_str = env.str(buf);
        Expression *width_exp = new E_intLit(width_str);

        replacement = new E_binary(size_exp, BIN_MULT, width_exp);
        replacement->tcheck(env, replacement);

        return env.getSimpleType(ST_UNSIGNED_INT);
      }
    }
  }

  return env.sizeofType(atype->getType(), size, NULL /*expr*/);
}

  
// Type check 'expr', given that it is being used to set the value of
// something with type 'target', and so we can use that as the basis
// for resolving the address of an overloaded function name.
void tcheckExpression_possibleAddrOfOverload
  (Env &env, Expression *&expr, Type *target)
{
  LookupSet set;
  tcheckExpression_set(env, expr, LF_TEMPL_PRIMARY, set);
  env.possiblySetOverloadedFunctionVar(expr, target, set);
}


Type *E_assign::itcheck_x(Env &env, Expression *&replacement)
{
  ArgumentInfoArray argInfo(2);
  tcheckArgumentExpression(env, target, argInfo[0]);
  tcheckArgumentExpression(env, src, argInfo[1]);

  // check for operator overloading
  {
    Type *ovlRet = resolveOverloadedBinaryOperator(
      env, replacement, this, target, src,
      toOverloadableOp(op, true /*assignment*/), argInfo);
    if (ovlRet) {
      this->type = ovlRet;
      return ovlRet;
    }
  }

  // TODO: make sure 'target' and 'src' make sense together with 'op'

  // this finalizes an overloaded function name if the use
  // of '=' was not overloadable
  env.possiblySetOverloadedFunctionVar(src, target->type, argInfo[1].overloadSet);

  return target->type;
}


Type *E_new::itcheck_x(Env &env, Expression *&replacement)
{
  // check the placement args
  {
    ArgumentInfoArray argInfo(placementArgs->count() + 1);
    placementArgs = tcheckArgExprList(placementArgs, env, argInfo);

    // TODO: check the environment for declaration of an operator 'new'
    // which accepts the given placement args
  }

  // typecheck the typeid in E_new context; it returns the
  // array size for new[] (if any)
  ASTTypeId::Tcheck tc(DF_NONE, DC_E_NEW);
  tc.newSizeExpr = &arraySize;
  atype = atype->tcheck(env, tc);

  // grab the type of the objects to allocate
  Type *t = atype->getType();

  // if the named type is an incomplete type, that will already have
  // been detected and reported (when 'atype' was tchecked), and 't'
  // will be the error type, which is safe to propagate into the code
  // below and beyond

  // The AST has the capability of recording whether argument parens
  // (the 'new-initializer' in the terminology of cppstd)
  // syntactically appeared, and this does matter for static
  // semantics; see cppstd 5.3.4 para 15.  However, for our purposes,
  // it will likely suffice to simply pretend that anytime 't' refers
  // to a class type, missing parens were actually present.
  if (t->isCompoundType() && !ctorArgs) {
    ctorArgs = new ArgExpressionListOpt(NULL /*list*/);
  }

  if (ctorArgs) {
    ArgumentInfoArray argInfo(ctorArgs->list->count() + 1);
    ctorArgs->list = tcheckArgExprList(ctorArgs->list, env, argInfo);
    Variable *ctor0 =
      outerResolveOverload_ctor(env, env.loc(), t, argInfo);
    // ctor0 can be null when the type is a simple type, such as an
    // int; I assume that ctor0 being NULL is the correct behavior in
    // that case
    ctorVar = env.storeVar(ctor0);
    compareCtorArgsToParams(env, ctor0, ctorArgs->list, argInfo);
  }

  return env.makePtrType(t);
}


Type *E_delete::itcheck_x(Env &env, Expression *&replacement)
{
  expr->tcheck(env, expr);

  Type *t = expr->type->asRval();   

  if (t->isGeneralizedDependent()) {
    // fine; in/k0020.cc
  }
  else if (!t->isPointer()) {
    env.error(t, stringc
      << "can only delete pointers, not `" << t->toString() << "'");
  }
  
  return env.getSimpleType(ST_VOID);
}


Type *E_throw::itcheck_x(Env &env, Expression *&replacement)
{
  if (expr) {
    expr->tcheck(env, expr);
  }
  else {
    // TODO: make sure that we're inside a 'catch' clause
  }

  return env.getSimpleType(ST_VOID);
}


Type *E_keywordCast::itcheck_x(Env &env, Expression *&replacement)
{
  if (env.lang.isCplusplus && hasTypeDefn(ctype)) {
    // 5.2.7p1: not allowed in dynamic_cast
    // 5.2.9p1: not allowed in static_cast
    // 5.2.10p1: not allowed in reinterpret_cast
    // 5.2.11p1: not allowed in const_cast
    return env.error(ctype->spec->loc, stringc 
      << "cannot define types in a " << toString(key));
  }

  ASTTypeId::Tcheck tc(DF_NONE, DC_E_KEYWORDCAST);
  ctype = ctype->tcheck(env, tc);
  expr->tcheck(env, expr);

  // TODO: make sure that 'expr' can be cast to 'type'
  // using the 'key'-style cast

  return ctype->getType();
}


Type *E_typeidExpr::itcheck_x(Env &env, Expression *&replacement)
{
  expr->tcheck(env, expr);
  return env.type_info_const_ref();
}


Type *E_typeidType::itcheck_x(Env &env, Expression *&replacement)
{
  ASTTypeId::Tcheck tc(DF_NONE, DC_E_TYPEIDTYPE);
  ttype = ttype->tcheck(env, tc);
  return env.type_info_const_ref();
}


Type *E_grouping::itcheck_x(Env &env, Expression *&replacement)
{
  LookupSet dummy;
  return itcheck_grouping_set(env, replacement, LF_NONE, dummy);
}

Type *E_grouping::itcheck_grouping_set(Env &env, Expression *&replacement,
                                       LookupFlags flags, LookupSet &set)
{
  tcheckExpression_set(env, expr, flags, set);
  
  // 2005-08-14: Let's try throwing away the E_groupings as part
  // of type checking.
  replacement = expr;

  return expr->type;
}


// --------------------- Expression constEval ------------------
// TODO: Currently I do not implement the notion of "value-dependent
// expression" (cppstd 14.6.2.3).  But, I believe a good way to do
// that is to extend 'constEval' so it can return a code indicating
// that the expression *is* constant, but is also value-dependent.

bool Expression::constEval(Env &env, int &result) const
{
  bool dependent;
  return constEval(env, result, dependent);
}

bool Expression::constEval(Env &env, int &result, bool &dependent) const
{
  dependent = false;

  ConstEval cenv(env.dependentVar);

  CValue val = constEval(cenv);
  if (val.isError()) {
    env.error(*(val.getWhy()));
    delete val.getWhy();
    return false;
  }              
  else if (val.isDependent()) {
    dependent = true;
    return true;
  }
  else if (val.isIntegral()) {
    result = val.getIntegralValue();
    return true;
  }
  else {
    env.error("expected integral-typed constant expression");
    return false;
  }
}


bool Expression::hasUnparenthesizedGT(Expression *&expr)
{
  if (expr->ambiguity) {
    Expression *origExpr = expr;

    // We are asking whether an ambiguous expression has an
    // unparenthesized greater-than operator (UGTO), because the
    // parser wants to reject such things.  But this expression is
    // ambiguous!  So, if some of the alternatives contain UGTO
    // but others do not, simply remove the UGTO alternatives and
    // then return false.  If they *all* have UGTO, return true.
    Expression **alt = &expr;
    while (*alt) {
      if ((*alt)->ihasUnparenthesizedGT()) {
        // remove this one from the list
        TRACE("cancel", "removed an ambiguous UGTO alternative");
        *alt = (*alt)->ambiguity;
      }
      else {
        // move to the next element
        alt = &( (*alt)->ambiguity );
      }
    }

    if (expr) {
      // at least one non-UGTO alternative remains
      return false;
    }
    else {
      // (in/c/dC0030.c) Do not leave 'expr' nullified, since that can
      // mess up other queries on this AST; instead, put back the
      // first one and nullify its ambiguity link.  This
      // interpretation should still be rejected, but this way it is a
      // well-formed AST.
      expr = origExpr;
      expr->ambiguity = NULL;

      // all have UGTO
      return true;
    }
  }

  // easy case
  return expr->ihasUnparenthesizedGT();
}

bool Expression::ihasUnparenthesizedGT()
{
  // recursively dig down into any subexpressions which syntactically
  // aren't enclosed in parentheses or brackets
  ASTSWITCH(Expression, this) {
    ASTCASE(E_funCall, f)
      return hasUnparenthesizedGT(f->func);

    ASTNEXT(E_fieldAcc, f)
      return hasUnparenthesizedGT(f->obj);

    ASTNEXT(E_unary, u)
      return hasUnparenthesizedGT(u->expr);

    ASTNEXT(E_effect, e)
      return hasUnparenthesizedGT(e->expr);

    ASTNEXT(E_binary, b)
      if (b->op == BIN_GREATER) {
        // all this just to find one little guy..
        return true;
      }

      return hasUnparenthesizedGT(b->e1) ||
             hasUnparenthesizedGT(b->e2);

    ASTNEXT(E_addrOf, a)
      return hasUnparenthesizedGT(a->expr);

    ASTNEXT(E_deref, d)
      return hasUnparenthesizedGT(d->ptr);

    ASTNEXT(E_cast, c)
      return hasUnparenthesizedGT(c->expr);

    ASTNEXT(E_cond, c)
      return hasUnparenthesizedGT(c->cond) ||
             hasUnparenthesizedGT(c->th) ||
             hasUnparenthesizedGT(c->el);

    ASTNEXT(E_assign, a)
      return hasUnparenthesizedGT(a->target) ||
             hasUnparenthesizedGT(a->src);

    ASTNEXT(E_delete, d)
      return hasUnparenthesizedGT(d->expr);

    ASTNEXT(E_throw, t)
      return t->expr && hasUnparenthesizedGT(t->expr);

    ASTDEFAULT
      // everything else, esp. E_grouping, is false
      return extHasUnparenthesizedGT();

    ASTENDCASE
  }
}

bool Expression::extHasUnparenthesizedGT()
{
  return false;
}


// can 0 be cast to 't' and still be regarded as a null pointer
// constant?
bool allowableNullPtrCastDest(CCLang &lang, Type *t)
{
  // C++ (4.10, 5.19)
  if (t->isIntegerType() || t->isEnumType()) {
    return true;
  }

  // C99 6.3.2.3: in C, void* casts are also allowed
  // bhackett: allowing this in C++ too. gcc preprocessed code contains
  // (void*)0 for NULL, which it can't even typecheck when fed back as input!

  if (// !lang.isCplusplus && 
      t->isPointerType() &&
      t->asPointerType()->atType->isVoid()) {
    return true;
  }
  
  return false;
}

SpecialExpr Expression::getSpecial(CCLang &lang) const
{
  ASTSWITCHC(Expression, this) {
    ASTCASEC(E_intLit, i)
      return i->i==0? SE_ZERO : SE_NONE;

    ASTNEXTC1(E_stringLit)
      return SE_STRINGLIT;

    // 9/23/04: oops, forgot this
    ASTNEXTC(E_grouping, e)
      return e->expr->getSpecial(lang);

    // 9/24/04: cppstd 4.10: null pointer constant is integral constant
    // expression (5.19) that evaluates to 0.
    // cppstd 5.19: "... only type conversions to integral or enumeration
    // types can be used ..."
    ASTNEXTC(E_cast, e)
      if (allowableNullPtrCastDest(lang, e->ctype->getType()) &&
          e->expr->getSpecial(lang) == SE_ZERO) {
        return SE_ZERO;
      }
      return SE_NONE;

    ASTDEFAULTC
      return SE_NONE;

    ASTENDCASEC
  }
}


// ------------------- FullExpression -----------------------
void FullExpression::tcheck(Env &env)
{
  expr->tcheck(env, expr);
}


// ExpressionListOpt

// ----------------------- Initializer --------------------
void IN_expr::tcheck(Env &env, Type *target)
{
  // TODO: check the initializer for compatibility with 'target'

  // limited form of checking: use 'target' to resolve 'e' if it
  // names an overloaded function

  // bhackett: bug? sometimes e is NULL.

  if (e) {
    tcheckExpression_possibleAddrOfOverload(env, e, target);
  }
}


// initialize 'type' with expressions drawn from 'initIter'
void initializeAggregate(Env &env, Type *type,
                         ASTListIterNC<Initializer> &initIter)
{
  if (initIter.isDone()) {
    return;
  }

  if (initIter.data()->isIN_compound()) {
    // match this entire bracketing with 'type'
    initIter.data()->tcheck(env, type);
    initIter.adv();
    return;
  }

  if (type->isArrayType()) {
    // initialize the array element type with successive initializers
    ArrayType *at = type->asArrayType();

    int limit = (at->hasSize()? at->size : -1);
    while (limit != 0 && !initIter.isDone()) {
      initializeAggregate(env, at->eltType, initIter);
      limit--;
    }
  }

  else if (type->isCompoundType()) {
    CompoundType *ct = type->asCompoundType();

    if (ct->isAggregate()) {
      // 8.5.1: initialize successive data fields with successive initializers
      SObjListIter<Variable> memberIter(ct->dataMembers);
      if (memberIter.isDone()) {    // no data fields?
        env.error(stringc << "can't initialize memberless aggregate "
                          << ct->keywordAndName());
        // type check against error type and advance to avoid infinite loop.
        initIter.data()->tcheck(env, env.errorType());
        initIter.adv();
      }
      while (!memberIter.isDone() && !initIter.isDone()) {
        initializeAggregate(env, memberIter.data()->type, initIter);
        memberIter.adv();
      }
    }
    else {
      Initializer *init = initIter.data();
      initIter.adv();

      // 8.5p14: initialize using a constructor
      
      if (init->isIN_ctor()) {
        init->tcheck(env, type);
        return;
      }
      
      xassert(init->isIN_expr());
      Expression *&arg = init->asIN_expr()->e;
      arg->tcheck(env, arg);

      ImplicitConversion ic = getImplicitConversion(env,
        arg->getSpecial(env.lang),
        arg->getType(),
        type,
        false /*destIsReceiver*/);
      if (!ic) {
        env.error(arg->getType(), stringc
          << "cannot convert initializer type `" << arg->getType()->toString()
          << "' to type `" << type->toString() << "'");
      }
    }
  }

  else {
    // down to an element type
    initIter.data()->tcheck(env, type);
    initIter.adv();
  }
}


void IN_compound::tcheck(Env &env, Type *type)
{
  // NOTE: I ignore the FullExpressionAnnot *annot

  // kick off a recursion for this list of initializers
  ASTListIterNC<Initializer> initIter(inits);
  initializeAggregate(env, type, initIter);

  // we should have consumed them all
  if (!initIter.isDone()) {   
    // This is a weak error because of designated initializers,
    // e.g., in/gnu/t0130.cc and in/c99/t0133.cc.  Once we get
    // the compound_init stuff folded into Elsa I should be able
    // to turn this into a real error.
    //
    // 2005-04-15: for the moment it is more annoying than helpful...
    //env.weakError(loc, stringc
    //  << "too many initializers (" << inits.count()
    //  << ") supplied for `" << type->toString() << "'");

    // tcheck the extra exprs anyway
    while (!initIter.isDone()) {
      initIter.data()->tcheck(env, type /*wrong but whatever*/);
      initIter.adv();
    }
  }
}


void IN_ctor::tcheck(Env &env, Type *destType)
{
  // check argument expressions
  ArgumentInfoArray argInfo(args->count() + 1);
  args = tcheckArgExprList(args, env, argInfo);

  // 8.5p14: if this was originally a copy-initialization (IN_expr),
  // and the source type is not the same class as or derived class
  // of the destination type, then we first implicitly convert the
  // source to the dest
  if (was_IN_expr) {
    Expression *src = args->first()->expr;
    Type *srcType = src->type;
    if (srcType->isCompoundType() &&
        destType->isCompoundType() &&
        srcType->asCompoundType()->hasBaseClass(destType->asCompoundType())) {
      // this is the scenario where we treat IN_expr the same as
      // IN_ctor, even for class types, so was_IN_expr is irrelevant
    }
    else {
      // first, do an implicit conversion
      ImplicitConversion ic = getImplicitConversion(env,
        src->getSpecial(env.lang),
        srcType,
        destType,
        false /*destIsReceiver*/);
      if (!ic) {
        env.error(srcType, stringc
          << "cannot convert initializer type `" << srcType->toString()
          << "' to target type `" << destType->toString() << "'");
        return;
      }
      
      // rewrite the AST to reflect the use of any user-defined
      // conversions
      if (ic.kind == ImplicitConversion::IC_USER_DEFINED) {
        if (ic.user->type->asFunctionType()->isConstructor()) {
          // wrap 'args' in an E_constructor
          TypeSpecifier *destTS = new TS_type(loc, loc, destType);
          E_constructor *ector = new E_constructor(destTS, args);
          ector->type = destType;
          ector->ctorVar = ic.user;
          args = FakeList<ArgExpression>::makeList(new ArgExpression(ector));

          // the variable will now be initialized by this 'ector',
          // which has type 'destType'
          srcType = destType;
        }
        else {
          // wrap 'args' in an E_funCall of a conversion function
          E_fieldAcc *efacc = new E_fieldAcc(src, new PQ_variable(loc, ic.user));
          efacc->type = ic.user->type;
          efacc->field = ic.user;
          E_funCall *efc = new E_funCall(efacc, FakeList<ArgExpression>::emptyList());
          efc->type = ic.user->type->asFunctionType()->retType;
          args = FakeList<ArgExpression>::makeList(new ArgExpression(efc));

          // variable initialized by result of calling the conversion
          srcType = efc->type;
        }
      }

      argInfo[1].special = SE_NONE;
      argInfo[1].type = srcType;
      ctorVar = env.storeVar(
        outerResolveOverload_ctor(env, loc, destType, argInfo));
        
      // don't do the final comparison; it will be confused by
      // the discrepancy between 'args' and 'argInfo', owing to
      // not having rewritten the AST above
      return;
    }
  }

  ctorVar = env.storeVar(
    outerResolveOverload_ctor(env, loc, destType, argInfo));
  compareCtorArgsToParams(env, ctorVar, args, argInfo);
}


// -------------------- TemplateDeclaration ---------------
void tcheckTemplateParameterList(Env &env, TemplateParameter *&src,
                                 SObjList<Variable> &tparams)
{
  xassert(tparams.isEmpty());
  int paramCt = 0;

  // keep track of the previous node in the list, so we can string
  // together the final disambiguated sequence
  TemplateParameter **prev = &src;

  TemplateParameter *tp = *prev;
  while (tp) {
    // disambiguate and check 'tp'
    tp = tp->tcheck(env);

    // string up the chosen one
    xassert(tp->ambiguity == NULL);     // these links should all be cut now
    *prev = tp;

    // add it to 'tparams' (reverse order)
    tparams.prepend(tp->var);
    tp->var->setParameterOrdinal(paramCt++);

    // follow the 'next' link in 'tp', as it was the chosen one
    prev = &(tp->next);
    tp = *prev;
  }

  // fix 'tparams'
  tparams.reverse();
}


void TemplateDeclaration::tcheck(Env &env)
{
  // disallow templates inside functions
  if (env.enclosingKindScope(SK_FUNCTION)) {
    env.error("template declaration in function or local class");
    return;
  }

  // make a new scope to hold the template parameters
  Scope *paramScope = env.enterScope(SK_TEMPLATE_PARAMS, "template declaration parameters");

  // check each of the parameters, i.e. enter them into the scope
  // and its 'templateParams' list
  tcheckTemplateParameterList(env, params, paramScope->templateParams);

  // mark the new scope as unable to accept new names, so
  // that the function or class being declared will be entered
  // into the scope above us
  paramScope->canAcceptNames = false;

  // in what follows, ignore errors that are not disambiguating
  //bool prev = env.setDisambiguateOnly(true);
  //
  // update: moved this inside Function::tcheck and TS_classSpec::tcheck
  // so that the declarators would still get full checking

  // check the particular declaration
  itcheck(env);

  // restore prior error mode
  //env.setDisambiguateOnly(prev);

  // remove the template argument scope
  env.exitScope(paramScope);
}


void TD_func::itcheck(Env &env)
{
  // check the function definition; internally this will get
  // the template parameters attached to the function type
  f->tcheck(env);
                                                                            
  // instantiate any instantiations that were requested but delayed
  // due to not having the definition
  env.instantiateForwardFunctions(f->nameAndParams->var);

  // 8/11/04: The big block of template code that used to be here
  // was superceded by activity in Declarator::mid_tcheck.
}


void TD_decl::itcheck(Env &env)
{
  if (env.secondPassTcheck) {
    // TS_classSpec is only thing of interest
    if (d->spec->isTS_classSpec()) {
      d->spec->asTS_classSpec()->tcheck(env, d->dflags);
    }
    return;
  }

  // cppstd 14 para 3: there can be at most one declarator
  // in a template declaration
  if (d->decllist->count() > 1) {
    env.error("there can be at most one declarator in a template declaration");
  }

  // is this like the old TD_class?
  bool likeTD_class = d->spec->isTS_classSpec() || d->spec->isTS_elaborated();

  // check the declaration; works like TD_func because D_func is the
  // place we grab template parameters, and that's shared by both
  // definitions and prototypes
  DisambiguateOnlyTemp disOnly(env, !likeTD_class);
  d->tcheck(env, DC_TD_DECL);
}


void TD_tmember::itcheck(Env &env)
{
  // just recursively introduce the next level of parameters; the
  // new take{C,F}TemplateInfo functions know how to get parameters
  // out of multiple layers of nested template scopes
  d->tcheck(env);
}


// ------------------- TemplateParameter ------------------
TemplateParameter *TemplateParameter::tcheck(Env &env)
{
  int dummy = 0;
  if (!ambiguity) {
    mid_tcheck(env, dummy);
    return this;
  }

  return resolveAmbiguity(this, env, "TemplateParameter", false /*priority*/, dummy);
}


void TemplateParameter::mid_tcheck(Env &env, int &dummy)
{
  itcheck(env, dummy);
}


void TP_type::itcheck(Env &env, int&)
{
  if (!name) {
    // name them all for uniformity
    name = env.getAnonName(loc, "tparam");
  }

  // cppstd 14.1 is a little unclear about whether the type name is
  // visible to its own default argument; but that would make no
  // sense, so I'm going to check the default type first
  //
  // 2005-04-08: No, the usual point of declaration rules (3.3.1p1)
  // apply, so it is visible in its default arg.  However, 14.1p14
  // then says it is illegal to use a template param in its own
  // default arg.  I'm not sure what I want to do about this...
  if (defaultType) {
    ASTTypeId::Tcheck tc(DF_NONE, DC_TP_TYPE);
    defaultType = defaultType->tcheck(env, tc);
  }

  // the standard is not clear about whether the user code should
  // be able to do this:
  //   template <class T>
  //   int f(class T &t)      // can use "class T" instead of just "T"?
  //   { ... }
  // my approach of making a TypeVariable, instead of calling
  // it a CompoundType with a flag for 'is type variable', rules
  // out the subsequent use of "class T" ...
  //
  // 2005-04-17: I noticed that in fact 7.1.5.3p2 addresses this, and
  // agrees it is not legal.

  // make a type variable for this thing
  TypeVariable *tvar = new TypeVariable(name);
  CVAtomicType *fullType = env.makeType(tvar);

  // make a typedef variable for this type
  this->var = env.makeVariable(loc, name, fullType,
                               DF_TYPEDEF | DF_TEMPL_PARAM);
  tvar->typedefVar = var;
  if (defaultType) {
    var->defaultParamType = defaultType->getType();
  }

  // if the default argument had an error, then do not add anything to
  // the environment, because the error could be due to an ambiguity
  // that is going to be resolved as *not* the current interpretation
  if (defaultType && defaultType->getType()->isError()) {
    return;
  }

  if (name) {
    // introduce 'name' into the environment
    if (!env.addVariable(var)) {
      env.error(stringc
        << "duplicate template parameter `" << name << "'",
        EF_NONE);
    }
  }
}


void TP_nontype::itcheck(Env &env, int&)
{
  // TODO: I believe I want to remove DF_PARAMETER.
  ASTTypeId::Tcheck tc(DF_PARAMETER | DF_TEMPL_PARAM, DC_TP_NONTYPE);

  // check the parameter; this actually adds it to the environment
  // too, so we don't need to do so here
  param = param->tcheck(env, tc);
  this->var = param->decl->var;
}


// -------------------- TemplateArgument ------------------
TemplateArgument *TemplateArgument::tcheck(Env &env, STemplateArgument &sarg)
{
  if (!ambiguity) {
    // easy case
    mid_tcheck(env, sarg);

    return this;
  }

  // generic resolution: whatever tchecks is selected
  return resolveAmbiguity(this, env, "TemplateArgument", false /*priority*/, sarg);
}

void TemplateArgument::mid_tcheck(Env &env, STemplateArgument &sarg)
{
  itcheck(env, sarg);
}

void TA_type::itcheck(Env &env, STemplateArgument &sarg)
{
  ASTTypeId::Tcheck tc(DF_NONE, DC_TA_TYPE);
  type = type->tcheck(env, tc);

  Type *t = type->getType();
  sarg.setType(t);
}

void TA_nontype::itcheck(Env &env, STemplateArgument &sarg)
{
  expr->tcheck(env, expr);
  env.setSTemplArgFromExpr(sarg, expr);
}


void TA_templateUsed::itcheck(Env &env, STemplateArgument &sarg)
{
  // nothing to do; leave 'sarg' as STA_NONE
}


// -------------------------- NamespaceDecl -------------------------
void ND_alias::tcheck(Env &env)
{
  // 2005-02-26: at this point the only thing being done is type
  // checking template arguments, which should not even be present,
  // but I do it anyway for uniformity
  tcheckPQName(original, env, NULL /*scope*/, LF_NONE);

  // find the namespace we're talking about
  Variable *origVar = env.lookupPQ_one(original, LF_ONLY_NAMESPACES);
  if (!origVar) {
    env.error(stringc
      << "could not find namespace `" << *original << "'");
    return;
  }
  xassert(origVar->isNamespace());   // meaning of LF_ONLY_NAMESPACES

  // is the alias already bound to something?
  Variable *existing = env.lookupVariable(alias, LF_INNER_ONLY);
  if (existing) {
    // 7.3.2 para 3: redefinitions are allowed only if they make it
    // refer to the same thing
    if (existing->isNamespace() &&
        existing->scope == origVar->scope) {
      return;     // ok; nothing needs to be done
    }
    else {
      env.error(stringc
        << "redefinition of namespace alias `" << alias
        << "' not allowed because the new definition isn't the same as the old");
      return;
    }
  }

  // make a new namespace variable entry
  Variable *v = env.makeVariable(env.loc(), alias, NULL /*type*/, DF_NAMESPACE);
  env.addVariable(v);

  // make it refer to the same namespace as the original one
  v->scope = origVar->scope;
  
  // note that, if one cares to, the alias can be distinguished from
  // the original name in that the scope's 'namespaceVar' still points
  // to the original one (only)
}


void ND_usingDecl::tcheck(Env &env)
{
  if (!name->hasQualifiers()) {
    env.error("a using-declaration requires a qualified name");
    return;
  }

  if (name->getUnqualifiedName()->isPQ_template()) {
    // cppstd 7.3.3 para 5
    env.error("you can't use a template-id (template name + template arguments) "
              "in a using-declaration");
    return;
  }

  // lookup the template arguments in the name
  tcheckPQName(name, env, NULL /*scope*/, LF_NONE);

  // find what we're referring to; if this is a template, then it
  // names the template primary, not any instantiated version
  LookupSet set;      
  env.lookupPQ(set, name, LF_TEMPL_PRIMARY);
  if (set.isEmpty()) {
    env.error(stringc << "undeclared identifier: `" << *name << "'");
    return;
  }

  Variable *origVar = set.first();
  if (origVar == env.dependentVar) {
    // if the lookup was dependent, add the name with dependent type
    // (k0048.cc, t0468.cc)
    Variable *v = env.makeVariable(name->loc, name->getName(), origVar->type, DF_NONE);
    
    // add with replacement; if the name already exists, then presumably
    // we are trying to make an overload set, but without a real function
    // type it all just degenerates to a dependent-typed set
    env.addVariable(v, true /*forceReplace*/);

    return;
  }

  // make aliases for everything in 'set'
  SFOREACH_OBJLIST_NC(Variable, set, iter) {
    env.makeUsingAliasFor(name->loc, iter.data());
  }

  // the example in 7.3.3p10 implies that the structure and enum
  // tags come along for the ride too
  //
  // for a long time this code has been written to only look at the
  // first element of 'set', and so far I have been unable to write
  // a test that shows any problem with that
  Scope *origScope = origVar->scope? origVar->scope : env.globalScope();

  // see if there is a name in the tag space of the same scope
  // where 'origVar' was found
  Variable *tag = origScope->lookup_one(origVar->name, env,
                                        LF_SUPPRESS_ERROR | LF_QUERY_TAGS |
                                        (name->hasQualifiers()? LF_QUALIFIED : LF_NONE));
  if (tag) {
    env.addTypeTag(tag);
  }
}


void ND_usingDir::tcheck(Env &env)
{
  tcheckPQName(name, env, NULL /*scope*/, LF_NONE);

  // find the namespace we're talking about
  Variable *targetVar = env.lookupPQ_one(name, LF_ONLY_NAMESPACES);
  if (!targetVar) {
    env.error(stringc
      << "could not find namespace `" << *name << "'");
    return;
  }
  xassert(targetVar->isNamespace());   // meaning of LF_ONLY_NAMESPACES
  Scope *target = targetVar->scope;
  
  // to implement transitivity of 'using namespace', add a "using"
  // edge from the current scope to the target scope, if the current
  // one has a name (and thus could be the target of another 'using
  // namespace')
  //
  // update: for recomputation to work, I need to add the edge
  // regardless of whether 'cur' has a name
  Scope *cur = env.scope();
  cur->addUsingEdge(target);

  if (cur->usingEdgesRefct == 0) {
    // add the effect of a single "using" edge, which includes
    // a transitive closure computation
    cur->addUsingEdgeTransitively(env, target);
  }
  else {
    // someone is using me, which means their transitive closure
    // is affected, etc.  let's just recompute the whole network
    // of active-using edges
    env.refreshScopeOpeningEffects();
  }
}


// EOF
