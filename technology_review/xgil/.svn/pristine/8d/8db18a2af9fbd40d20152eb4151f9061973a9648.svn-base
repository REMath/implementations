// integrity.h
// procedures for checking the the AST is well-formed, for
// various notions of well-formedness

#ifndef INTEGRITY_H
#define INTEGRITY_H

#include "astvisit.h"        // ASTVisitorEx
                    
// integrity checks:
//   - The AST must be unambiguous.
//   - No dependent types appear in concrete code.
class IntegrityVisitor : public ASTVisitorEx {
private:     // funcs
  void checkNontemplateType(Type *t);

public:      // funcs
  // ASTVisitorEx functions
  virtual void foundAmbiguous(void *obj, void **ambig, char const *kind);

  // ASTVisitor functions
  virtual bool visitDeclarator(Declarator *obj);
  virtual bool visitExpression(Expression *obj);
};

#endif // INTEGRITY_H
