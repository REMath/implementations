// cc_elaborate.h            see license.txt for copyright and terms of use
// semantic elaboration pass
// see also cc_elaborate.ast

#ifndef CC_ELABORATE_H
#define CC_ELABORATE_H


// The concept of semantic elaboration is that we provide, for many
// constructs in the language, equivalent alternative formulations in
// terms of a smaller set of primitive operations.  Then, an analysis
// can use the elaboration instead of building into itself the language
// spec's specified semantics.


#include "cc_ast.h"       // AST components, etc.
#include "macros.h"       // ENUM_BITWISE_OPS
#include "cc_ast_aux.h"   // class LoweredASTVisitor

// moved FullExpressionAnnot into fullexp.h to reduce dependencies
// in the #include graph
//
// dsw: made it into an AST class to simply serialization and because
// it has always been a rather odd-man-out and it seems natural as an
// AST class


// counter for generating unique throw clause names; NOTE: FIX: they
// must not be duplicated across translation units since they are
// global!  Thus, this must survive even multiple Env objects.
// (this is for elaboration)
extern int throwClauseSerialNumber;


// This enumeration lists all the activities performed by the elaboration
// visitor.  Each can be individually turned on or off, though all are
// on by default.
enum ElabActivities {
  // This replaces return-by-value for class-valued objects with
  // call-by-reference:
  //   - At every call site that would return by value, a temporary
  //     is created, and passed to the function as an additional
  //     argument.  Here, "passed" means the E_funCall or E_constructor
  //     has a 'retObj' pointer to the expression denoting the temporary.
  //   - In the callee, a special "<retVar>" variable is created; it is
  //     implicit that it gets its value from the passed temporary.  All
  //     S_returns are then rewritten to return nothing, but instead
  //     construct the <retVar> in their 'ctorStatement'.
  EA_ELIM_RETURN_BY_VALUE  = 0x0001,

  // At the end of a destructor, create a 'dtorStatement' which is the
  // sequence of dtors of superclasses and members.
  EA_MEMBER_DTOR           = 0x0002,

  // At member initializers (MemberInits), create a 'ctorStatement'
  // which explicates the construction of the superclass subobject or
  // class member as an E_constructor call.
  EA_MEMBER_CTOR           = 0x0004,

  // In constructors, for any superclasses or members that are not
  // explicitly initialized, insert MemberInits that invoke the
  // default (no-arg) constructor for the superclass or member.
  EA_IMPLICIT_MEMBER_CTORS = 0x0008,

  // Add inline definitions for the compiler-supplied declarations of
  // certain member functions: default ctor, copy ctor, assignment op,
  // and dtor.
  EA_IMPLICIT_MEMBER_DEFN  = 0x0010,

  // For each class-valued local or global variable, annotate its
  // declarator with a 'ctorStatement' and 'dtorStatement' that
  // construct and destruct the member, respectively.
  EA_VARIABLE_DECL_CDTOR   = 0x0020,

  // At throw and catch sites, add statements to construct, copy, and
  // destroy the global exception object that communicates thrown
  // object values from throw to catch.
  EA_GLOBAL_EXCEPTION      = 0x0040,

  // Eliminate pass-by-value for class-valued objects: at the call site,
  // create a temporary, and pass that.  Then, the callee can treat all
  // parameters (for class-valued params) as if they were pass by reference.
  EA_ELIM_PASS_BY_VALUE    = 0x0080,

  // Translate 'new' into allocation+construction, placing the
  // translation in the 'ctorStatement' of E_new.
  EA_TRANSLATE_NEW         = 0x0100,

  // Translate 'delete' into destruction+deallocation, placing the
  // translation in the 'dtorStatement' of E_delete.
  EA_TRANSLATE_DELETE      = 0x0200,

  // all flags above
  EA_ALL                   = 0x03FF,

  // Note that a number of the above activities create temporary
  // objects.  To support their deletion at the proper time,
  // cc_elaborate.ast adds FullExpressionAnnot objects to some AST
  // nodes, and elaboration registers the temporaries with them
  // accordingly.  An analysis should pay attention to the
  // FullExpressionAnnot objects so it can properly track temporary
  // object lifetimes.
};

ENUM_BITWISE_OPS(ElabActivities, EA_ALL)

// some special member functions
Variable *getDefaultCtor(StringTable&, CompoundType *ct);    // C(); might be NULL at any time
Variable *getCopyCtor(StringTable&, CompoundType *ct);       // C(C const &);
Variable *getAssignOperator(StringTable&, CompoundType *ct); // C& operator= (C const &);
Variable *getDtor(StringTable&, CompoundType *ct);           // ~C();     

// this visitor is responsible for conducting all the
// elaboration activities
// Intended to be used with LoweredASTVisitor
class ElabVisitor : private ASTVisitor {
public:      // data
  LoweredASTVisitor loweredVisitor; // use this as the argument for traverse()

  // similar fields to Env
  StringTable &str;
  TypeFactory &tfac;
  TranslationUnit *tunit;      // doh! out damned spot!

  // little trick: as code moves about it's convenient if 'env'
  // always works, even inside ElabVisitor methods
  ElabVisitor &env;            // refers to *this

  // stack of functions, topmost being the one we're in now
  ArrayStack<Function*> functionStack;

  // so that we can find the closest nesting S_compound for when we
  // need to insert temporary variables; its scope should always be
  // the current scope.
  ArrayStack<FullExpressionAnnot*> fullExpressionAnnotStack;

  // location of the most recent Statement.. used for approximate
  // loc info when visiting Expressions
  SourceLoc enclosingStmtLoc;

  // strings
  StringRef receiverName;

  // what we're doing; this defaults to EA_ALL, but the client
  // is free to modify it
  ElabActivities activities;

  // When true, we retain cloned versions of subtrees whose semantics
  // is captured (and therefore the tree obviated) by the elaboration.
  // When false, we just nullify thoee subtrees, which results in
  // sometimes-invalid AST, but makes some analyses happy anway.  This
  // defaults to false, but client can change it if desired.
  bool cloneDefunctChildren;

  // counters for generating unique temporary names; not unique
  // across translation units
  int tempSerialNumber;
  int e_newSerialNumber;

public:      // funcs
  // true if a particular activity is requested
  bool doing(ElabActivities a) const { return !!(activities & a); }
  
  // fresh names
  StringRef makeTempName();
  StringRef makeE_newVarName();
  StringRef makeThrowClauseVarName();
  StringRef makeCatchClauseVarName();
  
  // similar to a function in Env
  Variable *makeVariable(SourceLoc loc, StringRef name, 
                         Type *type, DeclFlags dflags);

  // syntactic convenience
  void push(FullExpressionAnnot *a) 
    { fullExpressionAnnotStack.push(a); }
  void pop(FullExpressionAnnot *a)
    { FullExpressionAnnot *tmp = fullExpressionAnnotStack.pop(); xassert(a == tmp); }

public:      // funcs
  // This section is organized like the .cc file, but all the comments
  // are in the .cc file, so look there first.

  // AST creation
  D_name *makeD_name(SourceLoc loc, Variable *var);
  Declarator *makeDeclarator(SourceLoc loc, Variable *var);
  Declaration *makeDeclaration(SourceLoc loc, Variable *var);
  Declarator *makeFuncDeclarator(SourceLoc loc, Variable *var);
  Function *makeFunction(SourceLoc loc, Variable *var,
                         FakeList<MemberInit> *inits,
                         S_compound *body);
  E_variable *makeE_variable(SourceLoc loc, Variable *var);
  E_fieldAcc *makeE_fieldAcc
    (SourceLoc loc, Expression *obj, Variable *field);
  E_funCall *makeMemberCall
    (SourceLoc loc, Expression *obj, Variable *func, FakeList<ArgExpression> *args);
  FakeList<ArgExpression> *emptyArgs();
  Expression *makeThisRef(SourceLoc loc);
  S_expr *makeS_expr(SourceLoc loc, Expression *e);
  S_compound *makeS_compound(SourceLoc loc);

  // makeCtor
  E_constructor *makeCtorExpr(
    SourceLoc loc,
    Expression *target,
    Type *type,
    Variable *ctor,
    FakeList<ArgExpression> *args);
  Statement *makeCtorStatement(
    SourceLoc loc,
    Expression *target,
    Type *type,
    Variable *ctor,
    FakeList<ArgExpression> *args);

  // makeDtor
  Expression *makeDtorExpr(SourceLoc loc, Expression *target,
                           Type *type);
  Statement *makeDtorStatement(SourceLoc loc, Expression *target,
                               Type *type);

  // cloning
  FakeList<ArgExpression> *cloneExprList(FakeList<ArgExpression> *args0);
  Expression *cloneExpr(Expression *e);

  // elaborateCDtors
  void elaborateCDtorsDeclaration(Declaration *decl);

  // elaborateCallSite
  Declaration *makeTempDeclaration
    (SourceLoc loc, Type *retType, Variable *&var /*OUT*/);
  Variable *insertTempDeclaration(SourceLoc loc, Type *retType);
  Expression *elaborateCallByValue
    (SourceLoc loc, Type *paramType, Expression *argExpr);
  Expression *elaborateCallSite(
    SourceLoc loc,
    FunctionType *ft,
    FakeList<ArgExpression> *args,
    bool artificalCtor);

  // elaborateFunctionStart
  void elaborateFunctionStart(Function *f);

  // completeNoArgMemberInits
  bool wantsMemberInit(Variable *var);
  MemberInit *findMemberInitDataMember
    (FakeList<MemberInit> *inits,
     Variable *memberVar);
  MemberInit *findMemberInitSuperclass
    (FakeList<MemberInit> *inits,
     CompoundType *superclass);
  void completeNoArgMemberInits(Function *ctor, CompoundType *ct);

  // make compiler-supplied member funcs
  Variable *makeCtorReceiver(SourceLoc loc, CompoundType *ct);
  MR_func *makeNoArgCtorBody(CompoundType *ct, Variable *ctor);
  MemberInit *makeCopyCtorMemberInit(
    Variable *target,
    Variable *srcParam,
    SourceLoc loc);
  MR_func *makeCopyCtorBody(CompoundType *ct, Variable *ctor);
  S_return *make_S_return_this(SourceLoc loc);
  S_expr *make_S_expr_memberCopyAssign
    (SourceLoc loc, Variable *member, Variable *other);
  Statement *make_statement_superclassCopyAssign
    (SourceLoc loc, CompoundType *w, Variable *other);
  void fill_S_compound_assignBody
    (SourceLoc loc, CompoundType *ct, Variable *other,
     ASTList<Statement> *stmts);
  MR_func *makeCopyAssignBody
    (SourceLoc loc, CompoundType *ct, Variable *assign);
  Statement *make_S_memberDtor
    (SourceLoc loc, Expression *member, CompoundType *memberType);
  void completeDtorCalls(
    Function *func,
    CompoundType *ct);
  MR_func *makeDtorBody(CompoundType *ct, Variable *dtor);

public:
  ElabVisitor(StringTable &str, TypeFactory &tfac, TranslationUnit *tunit);
  virtual ~ElabVisitor();

  // ASTVisitor funcs
  bool visitTopForm(TopForm *tf);
  bool visitFunction(Function *f);
  void postvisitFunction(Function *f);
  bool visitMemberInit(MemberInit *mi);
  void postvisitMemberInit(MemberInit *mi);
  bool visitTypeSpecifier(TypeSpecifier *ts);
  bool visitMember(Member *m);
  bool visitStatement(Statement *s);
  bool visitCondition(Condition *c);
  bool visitHandler(Handler *h);
  void postvisitHandler(Handler *h);
  bool visitExpression(Expression *e);
  bool visitFullExpression(FullExpression *fe);
  void postvisitFullExpression(FullExpression *fe);
  bool visitInitializer(Initializer *in);
  void postvisitInitializer(Initializer *in);
};


#endif // CC_ELABORATE_H
