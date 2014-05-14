// integrity.cc
// code for integrity.h

#include "integrity.h"         // this module


void IntegrityVisitor::foundAmbiguous(void *obj, void **ambig, char const *kind)
{
  // 2005-06-29: I have so far been unable to provoke this error by
  // doing simple error seeding, because it appears to be masked by a
  // check in the elaboration visitor regarding visiting certain lists
  // more than once.  Among other things, that means if there is a bug
  // along these lines, a user will discover it by seeing the
  // unfriendly list-visit assertion failure insteead of the message
  // here.  But, that stuff is wrapped up in the Daniel's lowered
  // visitor mechanism, which I don't want to mess with now.  Anyway,
  // I'm reasonably confident that this check will work properly.
  xfatal(toString(loc) << ": internal error: found ambiguous " << kind);
}


bool IntegrityVisitor::visitDeclarator(Declarator *obj)
{
  if (!ASTVisitorEx::visitDeclarator(obj)) {
    return false;
  }

  // make sure the type is not a DQT if we are not in a template
  if (!inTemplate) {
    checkNontemplateType(obj->var->type);
    checkNontemplateType(obj->type);
  }

  return true;
}

void IntegrityVisitor::checkNontemplateType(Type *t)
{
  if (t->containsGeneralizedDependent()) {
    xfatal(toString(loc) << ": internal error: found dependent type `"
                         << t->toString() << "' in non-template");
  }
}


bool IntegrityVisitor::visitExpression(Expression *obj)
{
  if (!ASTVisitorEx::visitExpression(obj)) {
    return false;
  }

  // 2005-08-18: I started to do this, then realized that these might
  // survive in template bodies.
  //
  // TODO: Make a way for ASTVisitorEx to communicate to visitors
  // whether they are in template bodies or not.
  #if 0
  if (obj->isE_grouping()) {
    xfatal(toString(loc) << ": internal error: found E_grouping after tcheck");
  }
  if (obj->isE_arrow()) {
    xfatal(toString(loc) << ": internal error: found E_arrow after tcheck");
  }
  #endif // 0

  return true;
}


// EOF
