// cc_ast_aux.h
// dsw: stuff I would like to put into cc.ast but I can't

#ifndef CC_AST_AUX_H
#define CC_AST_AUX_H

#include "sobjset.h"            // class SObjSet
#include "macros.h"             // ENUM_BITWISE_OPS
#include "cc_ast.h"             // ASTVisitor

// Note that LoweredASTVisitor and LoweredASTVisitorHelper work
// closely together

// I can't put LoweredASTVisitor and LoweredASTVisitorHelper into
// cc.ast because the class I inherit from, ASTVisitor, is generated
// at the end of cc.ast.gen.h

// forward
class LoweredASTVisitor;

// this class helps LoweredASTVisitor turn off visitation during
// uninstantiated templated bodies
class LoweredASTVisitorHelper : public ASTVisitor {
private:     // data
  LoweredASTVisitor &loweredVisitor;

  // also visit template definitions of primaries and partials
  bool primariesAndPartials;

  // set of the (primary) TemplateInfo objects the instantiations of
  // which we have visited; prevents us from visiting them twice
  SObjSet<TemplateInfo *> primaryTemplateInfos;

public:      // funcs
  LoweredASTVisitorHelper(LoweredASTVisitor &loweredVisitor0,
                          bool primariesAndPartials0)
    : loweredVisitor(loweredVisitor0)
    , primariesAndPartials(primariesAndPartials0)
  {}

  virtual bool visitDeclarator(Declarator *decltor);
  virtual bool visitTypeSpecifier(TypeSpecifier *spec);
  virtual bool visitFunction(Function *func);

  virtual bool subvisitTS_classSpec(TS_classSpec *spec);

  void oneTempl(Variable *var0);
  void oneContainer(Variable *container);
  void oneVariable(Variable *tinfoVar);
  void visitDeclarator0(Declarator *decltor);
  void visitTypeSpecifier0(TypeSpecifier *spec);
};


// there were too many boolean arguments to the LoweredASTVisitor
// ctor; FIX: make all visitors use these uniformly; FIX: Scott has
// some scheme to make these work better as flags but I can't find an
// example just now
enum VisitorFlags {
  VF_NONE                    = 0x00,
  VF_VISIT_ELAB              = 0x01, // visit the elaborated AST field as well
  VF_VISIT_PRIM_AND_PARTIALS = 0x02, // visit the template primaries and partials as well
  VF_CHECK_IS_TREE           = 0x04, // check the AST is a tree while we are at it

  VF_ALL                     = 0x07
};
ENUM_BITWISE_OPS(VisitorFlags, VF_ALL)


// extend the visitor to traverse the lowered AST, which includes
// additional AST that has bee elaborated into the AST, such as
// instantiated templates, implicit ctors and dtors, etc.
class LoweredASTVisitor : public DelegatorASTVisitor {
private:     // data
  LoweredASTVisitorHelper helper;

  // visit elaborated AST fields such as ctorStatement, etc., but
  // other than instantiated templates
  bool visitElaboratedAST;

  // FIX: this set for marking visited ast nodes is a rather strange
  // thing to have here as DelegatorASTVisitor also has one.  This one
  // is just used to avoid visiting templatized AST twice, which I
  // think can really legitimately otherwise occur given our template
  // represntation even if the AST is a tree.  The subclasses here
  // should intercept that duplication and return without calling the
  // overridden method of superclass which would otherwise fire an
  // assertion failure.
  SObjSet<void*> visitedTemplatizedASTNodes;

public:      // funcs
  LoweredASTVisitor(ASTVisitor *client0,
                    VisitorFlags flags0 = VF_CHECK_IS_TREE | VF_VISIT_ELAB)
    : DelegatorASTVisitor(client0, flags0 & VF_CHECK_IS_TREE)
    , helper(*this, flags0 & VF_VISIT_PRIM_AND_PARTIALS)
    , visitElaboratedAST(flags0 & VF_VISIT_ELAB)
  {}
  virtual ~LoweredASTVisitor() {}

  virtual bool visitFullExpressionAnnot(FullExpressionAnnot *fea);
  virtual bool visitDeclarator(Declarator *decltor);
  virtual bool visitTypeSpecifier(TypeSpecifier *spec);
  virtual bool visitTemplateDeclaration(TemplateDeclaration *templDecl);
  virtual bool visitFunction(Function *func);
  virtual bool visitMemberInit(MemberInit *mInit);
  virtual bool visitStatement(Statement *stmt);
  virtual bool visitExpression(Expression *expr);
  virtual bool visitHandler(Handler *handler);
  virtual bool visitFullExpression(FullExpression *fexpr);
  virtual bool visitInitializer(Initializer *initializer);

  virtual bool subvisitTS_classSpec(TS_classSpec *spec);

  // ensure idempotency of visiting AST
  bool visitedAST(void *ast);
};


// visitor for checking that the "raw" AST is a tree; note that the
// ctor arguments given to the parent are the sometime defaults of
// DelegatorASTVisitor, but we will not rely on that and also make the
// client code more self documenting by making this separate class
// here.
class IsTreeVisitor : public DelegatorASTVisitor {
public:
  IsTreeVisitor()
    : DelegatorASTVisitor(NULL /*client*/, true /*ensureOneVisit*/)
  {}
};


// visitor for checking that the "raw" AST is a tree *and* the
// "lowered" AST is a tree; the ensureOneVisit flag of our *parent* is
// the one that matters for checking that the *lowered* tree is a
// tree; LoweredASTVisitor inherits from DelegatorASTVisitor which the
// VF_CHECK_IS_TREE flag below tells to check that the *non*-lowered
// tree is a tree
class LoweredIsTreeVisitor : private IsTreeVisitor {
public:
  // used at creation site
  LoweredASTVisitor loweredVisitor;

  LoweredIsTreeVisitor()
    : loweredVisitor(this /*client*/, VF_VISIT_ELAB | VF_CHECK_IS_TREE)
  {}
};

#endif // CC_AST_AUX_H
