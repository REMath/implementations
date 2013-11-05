// kandr.h
// declarations of support functions for K&R parsing

#ifndef KANDR_H
#define KANDR_H

#include "cc_ast.h"         // AST

Function *makeKandRdefn(SourceLoc loc, Declaration *rds, IDeclarator *id,
                        S_compound *ds, S_compound *b);
void fixUpKandRFunctionDef
  (Declaration *rds, IDeclarator *id, S_compound *ds);
D_func *new_D_func_kandr
  (CCLang &lang,
   SourceLoc loc,
   IDeclarator *base,
   FakeList<ASTTypeId> *params,
   CVFlags cv,
   ExceptionSpec /*nullable*/ *exnSpec,
   FakeList<PQ_name> *kAndR_params);

#endif // KANDR_H
