// kandr.cc            see license.txt for copyright and terms of use
// support routines for the K&R extension

#include "kandr.h"          // this module
#include "generic_aux.h"    // genericSetNext
#include "cc_lang.h"        // CCLang


// implemented in implint.cc
bool filterOutImplIntFirstParam
  (SourceLoc loc,
   IDeclarator *base,
   FakeList<ASTTypeId> *&params);


// -------------------- AST extensions ---------------------
D_func *D_name::getD_func() {return NULL;}
D_func *D_pointer::getD_func() {return base->getD_func();}
D_func *D_reference::getD_func() {return base->getD_func();}
D_func *D_func::getD_func() {
  // you have to be careful that there may be another one nested down
  // inside if the user used this funky syntax:
  // int (*oink2(x))(int)
  D_func *df = base->getD_func();
  if (df) return df;
  else return this;
}
D_func *D_array::getD_func() {return base->getD_func();}
D_func *D_bitfield::getD_func() {return NULL;}
D_func *D_ptrToMember::getD_func() {return base->getD_func();}
D_func *D_grouping::getD_func() {return base->getD_func();}


void PQ_name::setNext(PQ_name *newNext)
{
  next = newNext;
}


// ---------------------- parsing support ---------------------
// return a parameter AST list constructed as if the K&R-defined
// function had been defined the usual way; NOTE: this imitates
// nonterm(FakeList<ASTTypeId>*) ParameterDeclarationList in cc.gr
// exactly because I didn't want to think hard about how to use
// Scott's datastructures correctly as I wasted so much time on that
// yesterday
FakeList<ASTTypeId>* kAndR_makeParamList
  (FakeList<PQ_name> *kAndR_params, PtrMap<const char, ASTTypeId> &declsForParams)
{
  if (!kAndR_params) return FakeList<ASTTypeId>::emptyList();
  PQ_name *pqName = kAndR_params->first();
  ASTTypeId *d = declsForParams.get(pqName->name);
  // if it has no declaration then it is an int
  if (!d) {
    d = new ASTTypeId
      (new TS_simple(pqName->loc, pqName->loc, ST_INT),
       new Declarator
       (new D_name
        (pqName->loc,
         // I'll make a new PQ_name to be safe that we have no
         // aliasing problems
         new PQ_name(pqName->loc, pqName->name)),
        NULL /*_init*/));
  } else {
    // mutate the location of the declaration to match that of the
    // place where the variable is first mentioned in the list; this
    // is only to allow cqual/tests/oldstyle2.c to pass
    d->decl->decl->loc = pqName->loc;
  }
  FakeList<ASTTypeId> *list = kAndR_makeParamList(kAndR_params->butFirst(), declsForParams);
  // FIX: why doesn't this segfault??; ah, because you can call
  // methods on null pointers as long as they are not virtual
  d->setNext(list->first());
  return FakeList<ASTTypeId>::makeList(d);
}

// create a Function definition with K&R params
Function *makeKandRdefn(SourceLoc loc, Declaration *rds, IDeclarator *id,
                        S_compound *ds, S_compound *b)
{
  Function *ret = new Function (
     rds->dflags,           // decl flags (static, extern, etc.)
     rds->spec,             // type specifier for return value
     new Declarator(id, NULL), // declarator with fn name, params
     NULL,                  // ctor member inits
     b,                     // function body statement
     NULL                   // exception handlers
     );
  fixUpKandRFunctionDef(rds, id, ds);
  return ret;
}

// convert ds to params and insert
void fixUpKandRFunctionDef
  (Declaration *rds, IDeclarator *id, S_compound *ds)
{
  // Find the declarations for these params
  // S_compound(ASTList<Statement> stmts) for each name, build an
  // ASTTypeId of the corresponding declarations.  Note that this
  // may involve taking apart a declaration with multiple
  // Declarator-s for a single DeclSpecifier.
  PtrMap<const char, ASTTypeId> declsForParams;
  FOREACH_ASTLIST_NC(Statement, ds->stmts, nameIter) {
    S_decl *sdecl = nameIter.data()->asS_decl();
    Declaration *declaration = dynamic_cast<Declaration*>(sdecl->decl);
    xassert(declaration);
    FAKELIST_FOREACH_NC(Declarator, declaration->decllist, dcltor) {
      // clone TypeSpecifier and Declarator
      ASTTypeId *atid = new ASTTypeId(declaration->spec->clone(), dcltor->clone());
      StringRef name = dcltor->decl->getDeclaratorId()->getName();
      declsForParams.add(name, atid);
    }
  }

  // Find the place where the params we are building should go.
  D_func *df = id->getD_func();
  xassert(df);
  xassert(!df->params);     //FakeList<ASTTypeId> *params

  // Find the "parameter" list which is just the names, without
  // types, "params" if a K&R function:
  //   FakeList<PQ_name> *kAndR_params
  // For each one, look up the declaration above and
  // build a Parameter for it.
  df->params = kAndR_makeParamList(df->kAndR_params, declsForParams);

  // ****

  rds->spec = NULL;           // stole it above (ownership transfer)
  delete rds;                 // was just a carrier of dflags/spec
}

D_func *new_D_func_kandr
  (CCLang &lang,
   SourceLoc loc,
   IDeclarator *base,
   FakeList<ASTTypeId> *params,
   CVFlags cv,
   ExceptionSpec /*nullable*/ *exnSpec,
   FakeList<PQ_name> *kAndR_params)
{
  if (lang.allowImplicitInt
      && !filterOutImplIntFirstParam(loc, base, params)) {
    return NULL;
  }
  return new D_func(loc, base, params, cv, exnSpec, kAndR_params);
}


// EOF
