// astvisit.cc
// code for astvisit.h

#include "astvisit.h"       // this module


ASTVisitorEx::ASTVisitorEx()
  : loc(SL_UNKNOWN)
{}


void ASTVisitorEx::visitFunctionInstantiation(Function *obj)
{
  obj->traverse(*this);
}


void ASTVisitorEx::foundAmbiguous(void *obj, void **ambig, char const *kind)
{}


bool ASTVisitorEx::visitFunction(Function *obj)
{
  // template with instantiations to visit?
  if (obj->isTemplate()) {
    // instantiations are concrete
    Restorer<bool> r(inTemplate, false);

    TemplateInfo *ti = obj->nameAndParams->var->templateInfo();
    SFOREACH_OBJLIST(Variable, ti->instantiations, iter) {
      Variable const *inst = iter.data();
      if (inst->templateInfo()->instantiatedFunctionBody()) {
        visitFunctionInstantiation(inst->funcDefn);
      }
    }
  }

  return true;
}

  
// wrap the unsafe cast
#define CAST_AMBIG(node) ((void**)(&((node)->ambiguity)))

bool ASTVisitorEx::visitPQName(PQName *obj)
{
  if (obj->loc != SL_UNKNOWN) {
    loc = obj->loc;
  }
  if (obj->isPQ_qualifier() &&
      obj->asPQ_qualifier()->ambiguity) {
    foundAmbiguous(obj, CAST_AMBIG(obj->asPQ_qualifier()), "PQ_qualifier");
  }
  return true;
}


// visit a node that has an ambiguity link
#define VISIT_W_AMBIG(type)                                        \
  bool ASTVisitorEx::visit##type(type *obj)                        \
  {                                                                \
    if (obj->ambiguity) {                                          \
      foundAmbiguous(obj, CAST_AMBIG(obj), obj->kindName());       \
    }                                                              \
    return true;                                                   \
  }

// visit a node that has a source location
#define VISIT_W_LOC(type)                         \
  bool ASTVisitorEx::visit##type(type *obj)       \
  {                                               \
    if (obj->loc != SL_UNKNOWN) {                 \
      loc = obj->loc;                             \
    }                                             \
    return true;                                  \
  }

// visit a node that has a source location and an ambiguity link
#define VISIT_W_LOC_AMBIG(type)                                    \
  bool ASTVisitorEx::visit##type(type *obj)                        \
  {                                                                \
    if (obj->loc != SL_UNKNOWN) {                                  \
      loc = obj->loc;                                              \
    }                                                              \
    if (obj->ambiguity) {                                          \
      foundAmbiguous(obj, CAST_AMBIG(obj), obj->kindName());       \
    }                                                              \
    return true;                                                   \
  }

VISIT_W_AMBIG(ASTTypeId)
VISIT_W_AMBIG(Declarator)
VISIT_W_AMBIG(Condition)
VISIT_W_AMBIG(Expression)
VISIT_W_AMBIG(ArgExpression)
VISIT_W_AMBIG(TemplateArgument)

VISIT_W_LOC(TypeSpecifier)
VISIT_W_LOC(Enumerator)
VISIT_W_LOC(Member)
VISIT_W_LOC(IDeclarator)
VISIT_W_LOC(Initializer)

VISIT_W_LOC_AMBIG(TopForm)
VISIT_W_LOC_AMBIG(Statement)
VISIT_W_LOC_AMBIG(TemplateParameter)

#undef VISIT_W_AMBIG
#undef VISIT_W_LOC
#undef VISIT_W_LOC_AMBIG
#undef CAST_AMBIG


// EOF
