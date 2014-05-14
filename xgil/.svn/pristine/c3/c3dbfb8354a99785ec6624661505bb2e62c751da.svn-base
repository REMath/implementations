// astvisit.h
// extension to the default ASTVisitor; this is an experimental
// replacement for the visitor classes in cc_ast_aux.h, so for
// now only I (Scott) will use this

#ifndef ASTVISIT_H
#define ASTVISIT_H

#include "cc_ast.h"       // ASTVisitor

class ASTVisitorEx : public ASTVisitor {
public:      // data
  // the most recent location we've seen
  SourceLoc loc;

public:      // funcs
  ASTVisitorEx();

  // 'visitFunction' calls this for template instantiations;
  // by default, this simply kicks off a traversal of 'obj'.
  virtual void visitFunctionInstantiation(Function *obj);

  // This is called when a node with a non-NULL ambiguity link is
  // encountered.  By default it does nothing.  'obj' is a pointer
  // to the node with the link; you'd have to cast it to do anything
  // with it.  'ambig' is a pointer to the ambiguity link itself;
  // this interface is unsound, letting you put any type of pointer
  // there, so be careful not to.  'kind' is the type of the node;
  // it's mostly meant for debugging and diagnostics, but in a pinch
  // it could be used for RTTI.
  virtual void foundAmbiguous(void *obj, void **ambig, char const *kind);

  // ASTVisitor functions
  #define DECL(type) \
    virtual bool visit##type(type *obj) /*user ;*/
  DECL(TopForm);
  DECL(Function);
  DECL(ASTTypeId);
  DECL(PQName);
  DECL(TypeSpecifier);
  DECL(Enumerator);
  DECL(Member);
  DECL(Declarator);
  DECL(IDeclarator);
  DECL(Statement);
  DECL(Condition);
  DECL(Expression);
  DECL(ArgExpression);
  DECL(Initializer);
  DECL(TemplateParameter);
  DECL(TemplateArgument);
  #undef DECL
};

#endif // ASTVISIT_H
