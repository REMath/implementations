// implint.h            see license.txt for copyright and terms of use
// ambiguity resolution for implicit-int

/*
  This is sort of an analogue to generic_amb.h, which contains
  the generic ambiguity resolution procedure.  The one in this
  file is for dealing with old-style C "implicit int", which
  for the moment is only parsed by oink's grammar.

  The basic parsing strategy is to have alternate syntactic forms for
  toplevel declarations that can have implicit ints, for example
  statement-decls with implicit ints.  This opposed to the more
  obvious strategy of making TypeSpecifier be optional, since that
  makes it more difficult to control where the ambiguities surface.

  When a declaration is parsed as using implicit int, its type
  specifier is set to TS_simple(ST_IMPLINT).  That way the ambiguity
  resolution procedure can tell which construct used implicit int.

  The resolution procedure itself is fairly simple: scan the list of
  ambiguous alternatives for those beginning with
  TS_simple(ST_IMPLINT).  If one exists, then check the first
  identifier (i.e. the 'name' of the bottom-most D_name) to see if it
  looks up to a type.  If so, then *reject* the implicit-int
  interpretation, because the C compiler would have lexed the name as
  a type and hence not used the implicit-int rule.  If the first name
  is not a type, then *accept* the implicit-int interpretation (and
  reject all the others), by the same reasoning.
*/

#ifndef IMPLINT_H
#define IMPLINT_H

#include "cc_ast.h"         // C++ AST
#include "cc_env.h"         // Env


// The 'hasImplicitInt' function returns true if the given node is
// using the implicit-int rule, and if so, also fills in the OUT
// parameter 'declarator', the declarator which has the name used to
// do disambiguation.
//
// There are several overloaded versions, one for each kind of node
// that has implicit-int ambiguity resolution to perform.  The
// templatized resolution procedure below automatically selects the
// appropriate one.

bool isImplicitInt(TypeSpecifier *ts)
{
  return ts->isTS_simple() &&
         ts->asTS_simple()->id == ST_IMPLINT;
}

bool hasImplicitInt(ASTTypeId *a, Declarator *&declarator)
{
  if (isImplicitInt(a->spec)) {
    declarator = a->decl;
    xassert(declarator);
    return true;
  }
  return false;
}

bool hasImplicitInt(Declaration *d, Declarator *&declarator)
{
  if (isImplicitInt(d->spec)) {
    declarator = d->decllist->first();
    xassert(declarator);
    return true;
  }
  return false;
}

bool hasImplicitInt(TopForm *tf, Declarator *&declarator)
{
  if (tf->isTF_decl()) {
    return hasImplicitInt(tf->asTF_decl()->decl, declarator);
  }
  if (tf->isTF_func()) {
    Function *f = tf->asTF_func()->f;
    if (isImplicitInt(f->retspec)) {
      declarator = f->nameAndParams;
      return true;
    }
  }
  return false;
}

bool hasImplicitInt(Statement *s, Declarator *&declarator)
{
  if (s->isS_decl()) {
    return hasImplicitInt(s->asS_decl()->decl, declarator);
  }
  return false;
}


// this returns a non-NULL value if it has selected the proper
// interpretation (or set of interpretations to further resolve)
// from the list; it returns NULL if it did not make any decision
template <class NODE>
NODE *resolveImplIntAmbig(Env &env, NODE *node)
{
  // find any of the ambiguities that are ST_IMPLINT and decide if we
  // want them or not
  for (NODE *s0 = node; s0; s0 = s0->ambiguity) {
    // Note that this loop does not continue once this 'if' tests as
    // true.
    Declarator *d0 = NULL;
    if (hasImplicitInt(s0, d0)) {
      xassert(env.lang.allowImplicitInt);
      xassert(d0);

      // if this is an implicit int declaration, then we allow it
      // *only if* the name of the declarator does not look up to a
      // type, even if the type interpretation is also wrong!  This
      // matches the gcc failure on this example for which both
      // interpretations (implicit int or not) fail:
      //   typedef int y;
      //   int main() {
      //     static *y;  // both interpretations fail here
      //     ++(*y);
      //   }

      // assert that all the declarators have the same name; NOTE: we
      // ignore any subsequent declarators for the purposes of
      // determining if we want the implicit-int interpretation
      //
      // We check that all the ambiguous Declarators (the various
      // parses of the *first* *user*-visible Declarator) all have the
      // same name; again we ignore the subsequent *user*-visible
      // Declarators
      //
      // NOTE: the name (and name1 below) should not be qualified but
      // we don't check that, trusting in the goodness of Odin
      StringRef name0 = d0->decl->getDeclaratorId()->getName();
      xassert(name0);
      for(Declarator *d1 = d0->ambiguity; d1; d1 = d1->ambiguity) {
        StringRef name1 = d1->decl->getDeclaratorId()->getName();
        xassert(name0 == name1);
      }
      // does this look up to a type?
      Variable *var = env.lookupVariable(name0);
      if (var && var->hasFlag(DF_TYPEDEF)) {
        // we reject the implicit-int interpretation
        if (s0 == node) {
          // by doing this the caller will re-write the ast node that
          // points to us
          return s0->ambiguity;
        } else {
          // chop s0 out of the list and repeat
          NODE *s2 = NULL;
          for(s2 = node; s2->ambiguity != s0; s2 = s2->ambiguity)
            {}
          xassert(s2->ambiguity == s0);
          s2->ambiguity = s2->ambiguity->ambiguity;
          // we do the whole thing over again in case there are two
          // implicit-int interpretations even though we think that
          // is not possible
          return node;
        }
      } else {
        // we keep the implicit-int interpretation
        s0->ambiguity = NULL;
        
        // there is no point to doing this here, since
        // TS_simple::itcheck has to do it also
        //simpSpec->id = ST_INT /*NOTE: was ST_IMPLINT*/;

        return s0;
      }
    }
  }
  return NULL;
}


#endif // IMPLINT_H
