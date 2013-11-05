// cc_env.h            see license.txt for copyright and terms of use
// Env class, which is the compile-time C++ environment

#ifndef CC_ENV_H
#define CC_ENV_H

#include "cc_type.h"      // Type, AtomicType, etc. (r)
#include "strobjdict.h"   // StrObjDict
#include "owner.h"        // Owner
#include "exc.h"          // xBase
#include "sobjlist.h"     // SObjList
#include "objstack.h"     // ObjStack
#include "sobjstack.h"    // SObjStack
#include "cc_ast.h"       // C++ ast components
#include "variable.h"     // Variable (r)
#include "cc_scope.h"     // Scope
#include "cc_err.h"       // ErrorList
#include "array.h"        // ArrayStack, ArrayStackEmbed
#include "builtinops.h"   // CandidateSet
#include "cc_lang.h"      // Bool3
#include "ptrmap.h"       // PtrMap
#include "mflags.h"       // MatchFlags

class StringTable;        // strtable.h
class CCLang;             // cc_lang.h
class TypeListIter;       // typelistiter.h
class SavedScopePair;     // fwd in this file
class MType;              // mtype.h
class ImplicitConversion; // implconv.h
class DelayedFuncInst;    // template.h


// type of collection to hold a sequence of scopes
// for nested qualifiers; it can hold up to 2 scopes
// before resorting to heap allocation
typedef ArrayStackEmbed<Scope*, 2> ScopeSeq;

// need to be able to print these out
void gdbScopeSeq(ScopeSeq &ss);

// flags for the template argument inference functions
enum InferArgFlags {
  IA_NONE            = 0,
  IA_NO_ERRORS       = 0,      // do not report errors
  IA_REPORT_ERRORS   = 0x01,   // report inference errors in Env
  IA_RECEIVER        = 0x02,   // passed arguments include potential receiver obj
  
  IA_ALL             = 0x03
};
ENUM_BITWISE_OPS(InferArgFlags, IA_ALL)

// bhackett: check invariants that should hold after type checking:
// - all expressions have been assigned a type.
class CheckTypesVisitor : public ASTVisitor {
public:
  virtual bool visitExpression(Expression *obj)
  {
    xassert(obj->type != NULL);
    return true;
  }
};

// the entire semantic analysis state
class Env : protected ErrorList {
protected:   // data
  // bound to '*this'; facilitates moving code into and out of Env
  Env &env;

  // stack of lexical scopes; first is innermost
  //
  // NOTE: If a scope has a non-NULL curCompound or namespaceVar,
  // then this list does *not* own it.  Otherwise it does own it.
  ObjList<Scope> scopes;

  // when true, all errors are ignored (dropped on floor) except:
  //   - errors with the 'disambiguates' flag set
  //   - unimplemented functionality
  // this is used when processing bodies of template classes and
  // functions, where we don't know anything about the type
  // parameters
  bool disambiguateOnly;

  // counter for constructing names
  //
  // dsw: 2005-04-18: made it static so multiple Envs won't collide
  static int anonCounter;

  // initially false, this becomes true once Env::Env has finished;
  // this is used to distinguish entities introduced automatically
  // at the start from those that appeared in the input file
  bool ctorFinished;
  
  // set of function templates whose instantiation has been delayed
  ObjList<DelayedFuncInst> delayedFuncInsts;

public:      // data
  // bhackett: enabled while processing annotation stub files,
  // where variable names do not need to resolve.
  bool annotating;

  // nesting level of disambiguation passes; 0 means not disambiguating;
  // this is used for certain kinds of error reporting and suppression
  int disambiguationNestingLevel;

  // when true, function bodies are tchecked; when false, they are
  // treated like prototypes; this lets class definitions delay
  // body tchecking until all the members have been entered into
  // the class scope
  bool checkFunctionBodies;

  // when true, we are re-typechecking part of a class definition,
  // hence the names encountered should already be declared, etc.
  bool secondPassTcheck;

  // list of error messages; during disambiguation, the existing
  // list is set aside, so 'errors' only has errors from the
  // disambiguation we're doing now (if any)
  ErrorList &errors;                 // reference to '*this'

  // if the disambiguator has temporarily hidden the "real" list of
  // errors, it can still be found here
  ErrorList *hiddenErrors;           // (nullable serf stackptr)

  // stack of locations at which template instantiation has been
  // initiated but not finished; this information can be used to
  // make error messages more informative, and also to detect
  // infinite looping in template instantiation
  ArrayStack<SourceLoc> instantiationLocStack;

  // string table for making new strings
  StringTable &str;

  // language options in effect
  CCLang &lang;

  // interface for making types
  TypeFactory &tfac;

  // client analyses may need to get ahold of all the Variables that I
  // made up, so this is a list of them; these don't include Variables
  // built for parameters of function types, but the functions
  // themselves appear here so the parameters are reachable (NOTE:
  // at the moment, I don't think anyone is using this information)
  ArrayStack<Variable*> madeUpVariables;

  // ---- BEGIN: special names ----
  // name under which conversion operators are looked up
  StringRef conversionOperatorName;                     
  
  // name under which constructors are looked up
  StringRef constructorSpecialName;             
  
  // name of the operator()() functions
  StringRef functionOperatorName;
  
  // "__receiver", a reference to the receiver object; it's a
  // parameter of methods
  StringRef receiverName;
  
  // "__other", the name of the parameter in implicit methods
  // that accept a reference to another object of the same type
  // (e.g. copy ctor)
  StringRef otherName;
  
  // linkage specification strings
  StringRef quote_C_quote;
  StringRef quote_C_plus_plus_quote;

  // a few more just to save string table lookups
  StringRef string__func__;
  StringRef string__FUNCTION__;
  StringRef string__PRETTY_FUNCTION__;
  StringRef string_main;

  StringRef special_checkType;
  StringRef special_getStandardConversion;
  StringRef special_getImplicitConversion;
  StringRef special_testOverload;
  StringRef special_computeLUB;
  StringRef special_checkCalleeDefnLine;
  StringRef special_test_mtype;
  StringRef special_cause_xfailure;
  // ---- END: special names ----

  // gcc __complex__ support
  StringRef string_realSelector;
  StringRef string_imagSelector;
  Variable *complexComponentFields[2 /*real=0, imag=1*/]
                                  [3 /*float=0, double=1, longdouble=2*/];

  // special variables associated with particular types
  Scope *dependentScope;                // (owner)
  Variable *dependentTypeVar;           // (serf)
  Variable *dependentVar;               // (serf)
  Variable *errorTypeVar;               // (serf)
  Variable *errorVar;                   // (serf)
  CompoundType *errorCompoundType;      // (serf)

  // Variable that acts like the name of the global scope; used in a
  // place where I want to return the global scope, but the function
  // is returning a Variable.. has DF_NAMESPACE
  Variable *globalScopeVar;             // (serf)

  // dsw: Can't think of a better way to do this, sorry.
  // sm: Do what?  Who uses this?  I don't see any uses in Elsa.
  Variable *var__builtin_constant_p;

  // operator function names, indexed by the operators they overload
  StringRef operatorName[NUM_OVERLOADABLE_OPS];

  // built-in operator function sets, indexed by operator
  ArrayStack<Variable*> builtinUnaryOperator[NUM_OVERLOADABLE_OPS];
  ObjArrayStack<CandidateSet> builtinBinaryOperator[NUM_OVERLOADABLE_OPS];

  // TODO: eliminate this!
  TranslationUnit *tunit;

  // when this is true, all template function instantiations are
  // delayed until the end of the translation unit
  bool delayFunctionInstantiation;

  // the following flags are used to disable certain parts of the
  // type checker due to maturity issues; they don't change during
  // the execution of the checker
  bool doFunctionTemplateBodyInstantiation;
  bool doCompareArgsToParams;
  bool doReportTemplateErrors;     // see doc/permissive.txt

  // when non-empty, the variable lookup results are collected and
  // compared to the text stored in this pointer; it is supplied via
  // an an 'asm' directive (see TF_asm::itcheck)
  string collectLookupResults;

private:     // funcs
  // old
  //CompoundType *instantiateClass(
  //  CompoundType *tclass, FakeList<TemplateArgument> *args);

  // these are intended to help build the initialization-time stuff,
  // not build functions that result from the user's input syntax
  Variable *declareFunctionNargs(
    Type *retType, char const *funcName,
    Type **argTypes, char const **argNames, int numArgs,
    FunctionFlags flags, 
    Type * /*nullable*/ exnType);

  Variable *declareFunction0arg(Type *retType, char const *funcName,
                                FunctionFlags flags = FF_NONE,
                                Type * /*nullable*/ exnType = NULL);

  Variable *declareFunction1arg(Type *retType, char const *funcName,
                                Type *arg1Type, char const *arg1Name,
                                FunctionFlags flags = FF_NONE,
                                Type * /*nullable*/ exnType = NULL);

  Variable *declareFunction2arg(Type *retType, char const *funcName,
                                Type *arg1Type, char const *arg1Name,
                                Type *arg2Type, char const *arg2Name,
                                FunctionFlags flags = FF_NONE,
                                Type * /*nullable*/ exnType = NULL);

  // NOTE: 3 arg missing; goes here.

  Variable *declareFunction4arg(Type *retType, char const *funcName,
                                Type *arg1Type, char const *arg1Name,
                                Type *arg2Type, char const *arg2Name,
                                Type *arg3Type, char const *arg3Name,
                                Type *arg4Type, char const *arg4Name,
                                FunctionFlags flags,
                                Type * /*nullable*/ exnType);

  void addGNUBuiltins();

  void setupOperatorOverloading();

  void addBuiltinUnaryOp(SimpleTypeId retId, OverloadableOp op, Type *x);

  void addBuiltinBinaryOp(SimpleTypeId retId, OverloadableOp op, Type *x, Type *y);
  void addBuiltinBinaryOp(SimpleTypeId retId, OverloadableOp op,
                          PredicateCandidateSet::PreFilter pre,
                          PredicateCandidateSet::PostFilter post,
                          bool isAssignment = false);
  void addBuiltinBinaryOp(OverloadableOp op, CandidateSet * /*owner*/ cset);

  PseudoInstantiation *createPseudoInstantiation
    (CompoundType *ct, ObjList<STemplateArgument> const &args);

  bool equivalentSignatures(FunctionType *ft1, FunctionType *ft2);
  bool equivalentTypes(Type const *t1, Type const *t2, 
                       MatchFlags mflags = MF_NONE);

  Variable *getPrimaryOrSpecialization
    (TemplateInfo *tinfo, ObjList<STemplateArgument> const &sargs);

  bool addVariableToScope(Scope *s, Variable *v, bool forceReplace=false);

  Scope *createScope(ScopeKind sk);

  void mergeDefaultArguments(SourceLoc loc, Variable *prior, FunctionType *type);

public:      // funcs
  Env(StringTable &str, CCLang &lang, TypeFactory &tfac, 
      TranslationUnit *tunit0 /*TODO: eliminate this!*/);
  virtual ~Env();      // 'virtual' only to silence stupid warning; destruction is not part of polymorphic contract

  // this function kicks off type checking for a translation unit;
  // it is not recursive (it should *not* call itself for namespaces)
  virtual void tcheckTranslationUnit(TranslationUnit *tunit);

  int getChangeCount() const { return scopeC()->getChangeCount(); }

  // scopes
  Scope *enterScope(ScopeKind sk, char const *forWhat);   // returns new Scope
  void exitScope(Scope *s);       // paired with enterScope()
  void extendScope(Scope *s);     // push onto stack, but don't own
  void retractScope(Scope *s);    // paired with extendScope()

  // the current, innermost scope
  Scope *scope() { return scopes.first(); }
  Scope const *scopeC() const { return scopes.firstC(); }

  // print out the variables in every scope with serialNumber-s
  void gdbScopes();

  // innermost scope that can accept names; the decl flags might
  // be used to choose exactly which scope to use
  Scope *acceptingScope(DeclFlags df = DF_NONE);
  Scope *typeAcceptingScope() { return acceptingScope(DF_TYPEDEF); }

  // innermost non-class, non-template, non-function-prototype scope
  Scope *outerScope();

  // innermost scope that can accept names, *other* than
  // the one we're in now
  Scope *enclosingScope();

  // return the nearest enclosing scope of kind 'k', or NULL if there
  // is none with that kind
  Scope *enclosingKindScope(ScopeKind k);
  Scope *globalScope() { return enclosingKindScope(SK_GLOBAL); }

  // essentially: enclosingKindScope(SK_CLASS)->curCompound;
  CompoundType *enclosingClassScope();
   
  // more flexible: don't begin looking for a scope with kind 'k'
  // until we pass 's' going up on the scope stack
  Scope *enclosingKindScopeAbove(ScopeKind k, Scope *s);

  bool inTemplate()
    { return !!enclosingKindScope(SK_TEMPLATE_PARAMS); }

  // do we need both this and 'inTemplate()'?
  bool inUninstTemplate() const
    { return disambiguateOnly; }

  // innermost scope that is neither SK_TEMPLATE_PARAMS nor SK_TEMPLATE_ARGS
  Scope *nonTemplateScope();

  // if we are in a template scope, go up one and then call
  // currentScopeEncloses(); FIX: I suspect this is not general enough
  // for what I really want
  bool currentScopeAboveTemplEncloses(Scope const *s);

  // true if the current scope contains 's' as a nested scope
  bool currentScopeEncloses(Scope const *s);

  // return the innermost scope that contains both the current
  // scope and 'target'
  Scope *findEnclosingScope(Scope *target);

  // set 'parentScope' for new scope 's', depending on whether
  // 'parent' is a scope that should be pointed at
  void setParentScope(Scope *s, Scope *parent);
  void setParentScope(Scope *s);     // compute 'parent' using current scope

  // bit of a hack: recompute what happens when all the active
  // scopes are opened; this is for using-directives
  void refreshScopeOpeningEffects();


  // source location tracking
  void setLoc(SourceLoc loc);                // sets scope()->curLoc
  SourceLoc loc() const;                     // gets scope()->curLoc
  string locStr() const { return toString(loc()); }
  string locationStackString() const;        // all scope locations
  string instLocStackString() const;         // inst locs only

  // insertion into the current scope; return false if the
  // name collides with one that is already there (but if
  // 'forceReplace' true, silently replace instead); if you
  // want to insert into a specific scope, use Scope::addVariable
  bool addVariable(Variable *v, bool forceReplace=false);
  bool addCompound(CompoundType *ct);
  bool addEnum(EnumType *et);
  bool addTypeTag(Variable *tag);

  // like 'addVariable' in that the 'scope' field gets set, but
  // nothing is added to the maps
  void registerVariable(Variable *v);

  // like 'addVariable', but if 'prevLookup' is not NULL then 'v' gets
  // added to prevLookup's overload set instead of the current scope;
  // it is *not* the case that all overloaded variables are added
  // using this interface
  void addVariableWithOload(Variable *prevLookup, Variable *v);
                                                         
  // 'addEnum', plus typedef variable creation and checking for duplicates
  Type *declareEnum(SourceLoc loc /*...*/, EnumType *et);


  // lookup in the environment (all scopes); if the name is not found,
  // return NULL, and emit an error if the name is qualified
  // (otherwise do not emit an error)
  Variable *lookupVariable  (StringRef name,     LookupFlags f=LF_NONE);

  // this variant returns the Scope in which the name was found
  Variable *lookupVariable(StringRef name, LookupFlags f, Scope *&scope);

  CompoundType *lookupCompound  (StringRef name,     LookupFlags f=LF_NONE);

  EnumType *lookupEnum  (StringRef name,     LookupFlags f=LF_NONE);

  // name + template args = inst
  Variable *applyPQNameTemplateArguments
    (Variable *var, PQName const *name, LookupFlags flags);

  // lookup a single qualifier; see comments at definition cc_env.cc
  Scope *lookupOneQualifier(
    Scope *startingScope,
    PQ_qualifier const *qualifier,
    bool &dependent,
    bool &anyTemplates,
    LookupFlags lflags = LF_NONE);

  // 'lookupOneQualifier', broken into two pieces; see implementation
  Variable *lookupOneQualifier_bareName(
    Scope *startingScope,
    PQ_qualifier const *qualifier,
    LookupFlags lflags);
  Scope *lookupOneQualifier_useArgs(
    Variable *qualVar,
    ObjList<STemplateArgument> const &sargs,
    bool &dependent,
    bool &anyTemplates,
    LookupFlags lflags);
  
  // extended interface capable of returning a set
  Variable *lookupVariable_set(LookupSet &candidates,
                               StringRef name, LookupFlags flags,
                               Scope *&foundScope);

  // push 'scope' and all its parents onto 'scopes'
  void getParentScopes(ScopeSeq &scopes, Variable *scopeVar);
  void getParentScopes(ScopeSeq &scopes, Scope *scope);
  void getParentScopesLimit(ScopeSeq &scopes, Scope *scope, Scope *limit);

  // extend/retract entire scope sequences
  void extendScopeSeq(ScopeSeq const &scopes);
  void retractScopeSeq(ScopeSeq const &scopes);
  
  // push/pop scopes that contain v's declaration (see implementation)
  void pushDeclarationScopes(Variable *v, Scope *stop);
  void popDeclarationScopes(Variable *v, Scope *stop);

  // if the innermost scope has some template parameters, take
  // them out and return them; otherwise return NULL; this is for
  // use by template *functions*
  TemplateInfo * /*owner*/ takeFTemplateInfo(bool allowInherited = true);

  // like the above, but for template *classes*
  TemplateInfo * /*owner*/ takeCTemplateInfo(bool allowInherited = true);

  // return a new name for an anonymous type; 'keyword' says
  // which kind of type we're naming
  StringRef getAnonName(SourceLoc loc, TypeIntr keyword);
  
  // more general
  StringRef getAnonName(SourceLoc loc, char const *why);

  // introduce a new compound type name; return the constructed
  // CompoundType's pointer in 'ct', after inserting it into 'scope'
  // (if that is not NULL)
  Type *makeNewCompound(CompoundType *&ct, Scope * /*nullable*/ scope,
                        StringRef name, SourceLoc loc,
                        TypeIntr keyword, bool forward);


  // this is for ErrorList clients
  virtual void addError(ErrorMsg * /*owner*/ obj);

  // diagnostic reports; all return ST_ERROR type
  Type *error(SourceLoc L, rostring msg, ErrorFlags eflags = EF_NONE);
  Type *error(rostring msg, ErrorFlags eflags = EF_NONE);
  Type *warning(SourceLoc L, rostring msg);
  Type *warning(rostring msg);
  Type *unimp(rostring msg);
  void diagnose3(Bool3 b, SourceLoc L, rostring msg, ErrorFlags eflags = EF_NONE);

  // this is used when something is nominally an error, but I think
  // or know that the code that detects the error is itself not yet
  // trustworthy, so I want to just accept the input with a warning
  void weakError(SourceLoc L, rostring msg);

  // diagnostics involving type clashes; will be suppressed
  // if the type is ST_ERROR
  Type *error(Type *t, rostring msg);
  Type *error(Type *t, SourceLoc loc, rostring msg);

  // just return ST_ERROR
  Type *errorType();

  // similarly for ST_DEPENDENT
  Type *dependentType();

  // set 'disambiguateOnly' to 'val', returning prior value
  bool setDisambiguateOnly(bool val);
  bool onlyDisambiguating() const { return disambiguateOnly; }

  // return true if the given list of errors contain any which
  // are disambiguating errors
  bool hasDisambErrors() const { return errors.hasDisambErrors(); }

  // return true if environment modifications should be suppressed
  // because of disambiguating errors
  bool disambErrorsSuppressChanges() const
    { return disambiguationNestingLevel>0 && hasDisambErrors(); }

  // number of errors; intended to be called after type checking,
  // to see how many errors (if any) resulted
  int numErrors() const { return errors.numErrors(); }

  // This is the error mode used for errors that I want to be
  // EF_STRONG (reported even in templates) while implementing new
  // features, but EF_NONE (not reported in templates) when trying to
  // get big testcases through.
  ErrorFlags maybeEF_STRONG() const;

  // report on unsearched base classes; "" if none
  string unsearchedDependentBases();

  // return value for (some...) erroneous lookups
  Variable *lookupErrorObject(LookupFlags flags);

  // when true, operator expressions are checked to see if they
  // are to be treated as calls to overloaded operator functions
  bool doOperatorOverload() const;

  // makes a function type that returns ST_CDTOR and accepts no params
  // (other than the receiver object of type 'ct')
  FunctionType *makeDestructorFunctionType(SourceLoc loc, CompoundType *ct);

  // similar to above, except its flagged with FF_CTOR, and the caller
  // must call 'doneParams' when it has finished adding parameters
  FunctionType *beginConstructorFunctionType(SourceLoc loc, CompoundType *ct);

  // TypeFactory funcs; all of these simply delegate to 'tfac'
  CVAtomicType *makeCVAtomicType(AtomicType *atomic, CVFlags cv)
    { return tfac.makeCVAtomicType(atomic, cv); }
  PointerType *makePointerType(CVFlags cv, Type *atType)
    { return tfac.makePointerType(cv, atType); }
  Type *makeReferenceType(Type *atType)
    { return tfac.makeReferenceType(atType); }
  FunctionType *makeFunctionType(Type *retType)
    { return tfac.makeFunctionType(retType); }
  void doneParams(FunctionType *ft)
    { tfac.doneParams(ft); }
  ArrayType *makeArrayType(Type *eltType, int size = ArrayType::NO_SIZE)
    { return tfac.makeArrayType(eltType, size); }

  // (this does the work of the old 'makeMadeUpVariable')
  Variable *makeVariable(SourceLoc L, StringRef n, Type *t, DeclFlags f);

  CVAtomicType *getSimpleType(SimpleTypeId st, CVFlags cv = CV_NONE)
    { return tfac.getSimpleType(st, cv); }
  CVAtomicType *makeType(AtomicType *atomic)
    { return tfac.makeType(atomic); }
  Type *makePtrType(Type *type)
    { return tfac.makePtrType(type); }

  // others are more obscure, so I'll just call into 'tfac' directly
  // in the places I call them
                                                              
  // if in a context where an implicit receiver object is available,
  // return its type; otherwise return NULL
  Type *implicitReceiverType();

  // create the receiver object parameter for use in a FunctionType
  Variable *receiverParameter(SourceLoc loc, NamedAtomicType *nat, CVFlags cv,
                              D_func *syntax = NULL);

  // standard conversion 4.1, 4.2, and 4.3
  Type *operandRval(Type *t);

  // get 'std::type_info const &'
  Type *type_info_const_ref();

  // create a built-in candidate for operator overload resolution
  Variable *createBuiltinUnaryOp(Type *retType, OverloadableOp op, Type *x);
  Variable *createBuiltinBinaryOp(Type *retType, OverloadableOp op, Type *x, Type *y);

  // several steps of the declaration creation process, broken apart
  // to aid sharing among D_name_tcheck and makeUsingAliasFor; best
  // to look at their implementations and the comments therein
  Variable *lookupVariableForDeclaration
    (Scope *scope, StringRef name, Type *type, CVFlags this_cv);
  OverloadSet *getOverloadForDeclaration(Variable *&prior, Type *type);
  Variable *createDeclaration(
    SourceLoc loc,
    StringRef name,
    Type *type,
    DeclFlags dflags,
    Scope *scope,
    CompoundType *enclosingClass,
    Variable *prior,
    OverloadSet *overloadSet
  );

  // compare types for equality; see extensive comment at
  // implementation
  bool almostEqualTypes(Type const *t1, Type const *t2,
                        MatchFlags mflags = MF_NONE);

  // create a "using declaration" alias
  void makeUsingAliasFor(SourceLoc loc, Variable *origVar);

  // see comments at implementation site
  void handleTypeOfMain(SourceLoc loc, Variable *prior, Type *&type);

  // pass Variable* through this before storing in the AST, so
  // that the AST only has de-aliased pointers (if desired);
  // a NULL argument is passed through unchanged
  Variable *storeVar(Variable *var);

  // this version will do pass-through if 'var' or the thing to which
  // it is aliased has an overload set; it's for those cases where
  // subsequent overload resolution needs to pick from the set, before
  // de-aliasing happens
  Variable *storeVarIfNotOvl(Variable *var);

  // points of extension: These functions do nothing in the base
  // Elsa parser, but can be overridden in client analyses to
  // hook into the type checking process.  See their call sites in
  // cc_tcheck.cc for more info on when they're called.

  virtual void checkFuncAnnotations(FunctionType *ft, D_func *syntax);

  // this is called after all the fields of 'ct' have been set, and
  // we've popped its scope off the stack
  virtual void addedNewCompound(CompoundType *ct);

  // return # of array elements initialized
  virtual int countInitializers(SourceLoc loc, Type *type, IN_compound const *cpd);

  // called when a variable is successfully added; note that there
  // is a similar mechanism in Scope itself, which can be used when
  // less context is necessary
  virtual void addedNewVariable(Scope *s, Variable *v);

  // search in an overload set for an element, given its type
  Variable *findInOverloadSet(OverloadSet *oset,
                              FunctionType *ft, CVFlags receiverCV);
  Variable *findInOverloadSet(OverloadSet *oset,
                              FunctionType *ft);   // use ft->getReceiverCV()

  // 7/27/04: removed:
  //   make_PQ_fullyQualifiedName
  //   make_PQ_qualifiedName
  //   make_PQ_possiblyTemplatizedName
  //   make_PQ_templateArgs
  //   make_PQ_fullyQualifiedDtorName
  //   buildASTTypeId
  //   inner_buildASTTypeId
  //   buildTypedefSpecifier
  
  // 2005-02-14: partially resurrected
  PQName *makeFullyQualifiedName(Scope *s, PQName *name);
  PQName *makeQualifiedName(Scope *s, PQName *name);
  /*fakelist*/TemplateArgument *makeTemplateArgs(TemplateInfo *ti);
  ASTTypeId *buildASTTypeId(Type *type);

  // make AST nodes, as if they have been tcheck'd
  E_intLit *build_E_intLit(int i);
  E_variable *build_E_variable(Variable *var);
  E_addrOf *build_E_addrOf(Expression *underlying);

  // make a function type for an implicitly declared function at its
  // call site: "int ()()"
  FunctionType *makeImplicitDeclFuncType();

  // make function variable for an implicitly declared function at its
  // call site with type makeImplicitDeclFuncType() above
  Variable *makeImplicitDeclFuncVar(StringRef name);

  // declare a function that can accept basically anything; mainly
  // used for functions the translator itself interprets
  Variable *declareSpecialFunction(char const *name);

  // see implementation; this is here b/c gnu.cc wants to call it
  Type *computeArraySizeFromCompoundInit(SourceLoc tgt_loc, Type *tgt_type,
                                         Type *src_type, Initializer *init);
                                                          
  // if 'type' is not a complete type, attempt to make it into one
  // (by template instantiation); if it cannot be, then emit an
  // error message (using 'action') and return false
  bool ensureCompleteType(char const *action, Type *type);
  bool ensureCompleteCompound(char const *action, CompoundType *ct);

  // support for cppstd 13.4; see implementations for more details
  Variable *getOverloadedFunctionVar(Expression *e);
  void setOverloadedFunctionVar(Expression *e, Variable *selVar);
  Variable *pickMatchingOverloadedFunctionVar(LookupSet &set, Type *type);
  void possiblySetOverloadedFunctionVar(Expression *expr, Type *paramType,
                                        LookupSet &set);

  // support for 3.4.2
  void getAssociatedScopes(SObjList<Scope> &associated, Type *type);
  void associatedScopeLookup(LookupSet &candidates, StringRef name,
                             ArrayStack<Type*> const &argTypes, LookupFlags flags);
  void addCandidates(LookupSet &candidates, Variable *var);

  // see comments at implementation
  void checkForQualifiedMemberDeclarator(Declarator *decl);

  Scope *createNamespace(SourceLoc loc, StringRef name);

  // ensureClassBodyInstantiated, then CompoundType::getSubobjects
  void getSubobjects(SObjList<BaseClassSubobj const> &dest,
                     CompoundType *ct);

  // Evaluate a 'sizeof' applied to type 't', store the result in
  // 'size', and return the type of the 'sizeof' expression itself.
  // If 't' was derived from an expression, it is passed as 'expr'.
  Type *sizeofType(Type *t, int &size, Expression * /*nullable*/ expr);

  // ------------ new lookup mechanism ---------------
private:     // funcs
  void unqualifiedLookup(LookupSet &set, Scope * /*nullable*/ scope,
                         StringRef name, LookupFlags flags);
  Variable *lookupScopeVar(Scope * /*nullable*/ scope, StringRef name,
                           LookupFlags flags);
  void finishDependentQType(LookupSet &set, DependentQType * /*nullable*/ dqt,
                            PQName *name);
  void checkTemplateKeyword(PQName *name);

public:      // funcs
  // this is the main lookup function in the new design
  void lookupPQ(LookupSet &set, PQName *name, LookupFlags flags);

  // effectively, this is a second entry point to 'lookupPQ'
  void lookupPQ_withScope(LookupSet &set, PQName *name, LookupFlags flags, Scope *scope);

  // do the last step of qualified lookup, where the qualifiers
  // denoted 'scope' and 'name' is the last element of the chain
  void unqualifiedFinalNameLookup(LookupSet &set, Scope *scope,
                                  PQName *name, LookupFlags flags);

  // yield just the first element of the lookup set, if any; the
  // context is going to reject a function name anyway (so it does
  // not matter if there is more than one)
  Variable *lookupPQ_one(PQName *name, LookupFlags flags);
  Variable *unqualifiedLookup_one(StringRef name, LookupFlags flags);
  Variable *unqualifiedFinalNameLookup_one(Scope *scope, PQName *name,
                                           LookupFlags flags);

  // lookup "~ct->name" in 'ct'
  void lookupClassDestructor(LookupSet &set, CompoundType *ct,
                             LookupFlags flags);
  
  // handling of DQTs in type specifiers
  Type *resolveDQTs(SourceLoc loc, Type *t);
  Type *resolveDQTs_atomic(SourceLoc loc, AtomicType *t);
  CompoundType *getMatchingTemplateInScope
    (CompoundType *primary, ObjList<STemplateArgument> const &sargs);
  AtomicType *resolveDQTs_pi(SourceLoc loc, PseudoInstantiation *pi);

  // ------------ template instantiation stuff ------------
  // the following methods are implemented in template.cc
private:     // template funcs
  CompoundType *findEnclosingTemplateCalled(StringRef name);

  void transferTemplateMemberInfo
    (SourceLoc instLoc, TS_classSpec *source,
     TS_classSpec *dest, ObjList<STemplateArgument> const &sargs);
  void transferTemplateMemberInfo_typeSpec
    (SourceLoc instLoc, TypeSpecifier *srcTS, CompoundType *sourceCT,
     TypeSpecifier *destTS, ObjList<STemplateArgument> const &sargs);
  void transferTemplateMemberInfo_one
    (SourceLoc instLoc, Variable *srcVar, Variable *destVar,
     ObjList<STemplateArgument> const &sargs);
  void transferTemplateMemberInfo_membert
    (SourceLoc instLoc, Variable *srcVar, Variable *destVar,
     ObjList<STemplateArgument> const &sargs);

  void insertTemplateArgBindings
    (Variable *baseV, SObjList<STemplateArgument> const &sargs);
  void insertTemplateArgBindings
    (Variable *baseV, ObjList<STemplateArgument> const &sargs);
  bool insertTemplateArgBindings_oneParamList
    (Scope *scope, Variable *baseV, SObjListIter<STemplateArgument> &argIter,
     SObjList<Variable> const &params);
  void deleteTemplateArgBindings(Scope *limit = NULL);

  void mapPrimaryArgsToSpecArgs(
    Variable *baseV,
    ObjList<STemplateArgument> &partialSpecArgs,
    ObjList<STemplateArgument> &primaryArgs);
  void mapPrimaryArgsToSpecArgs_oneParamList(
    SObjList<Variable> const &params,
    MType &match,
    ObjList<STemplateArgument> &partialSpecArgs);

  Variable *findCompleteSpecialization(TemplateInfo *tinfo,
                                       ObjList<STemplateArgument> const &sargs);
  void bindParametersInMap(MType &map, TemplateInfo *tinfo,
                           SObjList<STemplateArgument> const &sargs);
  void bindParametersInMap(MType &map,
                           SObjList<Variable> const &params,
                           SObjListIter<STemplateArgument> &argIter);

  Type *pseudoSelfInstantiation(CompoundType *ct, CVFlags cv);

  Variable *makeInstantiationVariable(Variable *templ, Type *instType);

  bool supplyDefaultTemplateArguments
    (TemplateInfo *primaryTI,
     ObjList<STemplateArgument> &dest,
     SObjList<STemplateArgument> const &src);
  STemplateArgument *makeDefaultTemplateArgument
    (Variable const *param, MType &map);

  Variable *instantiateClassTemplate_or_PI
    (CompoundType *ct, ObjList<STemplateArgument> const &args);
  
public:      // template funcs
  void setSTemplArgFromExpr(STemplateArgument &sarg, Expression *expr);
  STemplateArgument variableToSTemplateArgument(Variable *var);

  // load the bindings with any explicit template arguments; return true if successful
  bool loadBindingsWithExplTemplArgs(Variable *var, ObjList<STemplateArgument> const &args,
                                     MType &match, InferArgFlags iflags);
  // infer template arguments from the function arguments; return true if successful
  bool inferTemplArgsFromFuncArgs(Variable *var,
                                  TypeListIter &argsListIter,
//                                    FakeList<ArgExpression> *funcArgs,
                                  MType &match,
                                  InferArgFlags iflags);
  // get both the explicit and implicit function template arguments
  bool getFuncTemplArgs
    (MType &match,
     ObjList<STemplateArgument> &sargs,
     PQName const *final,
     Variable *var,
     TypeListIter &argListIter,
     InferArgFlags iflags);
  void getFuncTemplArgs_oneParamList
    (MType &match,
     ObjList<STemplateArgument> &sargs,
     InferArgFlags iflags,
     bool &haveAllArgs,
     //ObjListIter<STemplateArgument> &piArgIter,
     SObjList<Variable> const &paramList);
  bool getArgumentsFromMatch
    (MType &match, ObjList<STemplateArgument> &sargs,
     InferArgFlags iflags, Variable *primary);

  // Given a primary, find the most specific specialization for the
  // given template arguments 'sargs'; for full generality we allow
  // the primary itself as a "trivial specialization" and may return
  // that.
  Variable *findMostSpecific(Variable *baseV, ObjList<STemplateArgument> const &sargs);

  // Prepare the argument scope for the present typechecking of the
  // cloned AST for effecting the instantiation of the template;
  // Please see Scott's extensive comments at the implementation.
  void prepArgScopeForTemlCloneTcheck
    (ObjList<SavedScopePair> &poppedScopes, SObjList<Scope> &pushedScopes, 
     Scope *foundScope);

  // Undo prepArgScopeForTemlCloneTcheck().
  void unPrepArgScopeForTemlCloneTcheck
    (ObjList<SavedScopePair> &poppedScopes, SObjList<Scope> &pushedScopes);

  // function template instantiation chain
  Variable *instantiateFunctionTemplate
    (SourceLoc loc,
     Variable *primary,
     ObjList<STemplateArgument> const &sargs);
  Variable *instantiateFunctionTemplate
    (SourceLoc loc, Variable *primary, MType &match);
  void ensureFuncBodyTChecked(Variable *instV);    // try inst defn
  void instantiateFunctionBody(Variable *instV);   // inst defn
  void instantiateFunctionBodyNow(Variable *instV, SourceLoc loc);

  // given a template function that was just made non-forward,
  // instantiate all of its forward-declared instances
  void instantiateForwardFunctions(Variable *primary);

  // ensure that at least 'neededDefaults' default args are available
  void instantiateDefaultArgs(Variable *instV, int neededDefaults);

  // class template instantiation chain
  Variable *instantiateClassTemplate               // inst decl 1
    (SourceLoc loc,
     Variable *primary,
     SObjList<STemplateArgument> const &sargs);
  Variable *instantiateClassTemplate               // inst decl 2
    (SourceLoc loc,
     Variable *primary,
     ObjList<STemplateArgument> const &sargs);
  void instantiateClassBody(Variable *inst);       // inst defn

  // instantiate the given class' body, *if* it is an instantiation
  // and instantiation is possible but hasn't already been done; note
  // that most of the time you want to call ensureCompleteType, not
  // this function
  void ensureClassBodyInstantiated(CompoundType *ct);
        
  // do 'ensureClassBodyInstantiated' for all parameters
  void instantiateTemplatesInParams(FunctionType *ft);
       
  // instantiate functions used in 'ic'
  void instantiateTemplatesInConversion(ImplicitConversion &ic);

  // given a template class that was just made non-forward,
  // instantiate all of its forward-declared instances
  void instantiateForwardClasses(Variable *baseV);

  // given a class or function template instantiation, process
  // an "explicit instantiation" (14.7.2) request for it
  void explicitlyInstantiate(Variable *inst, DeclFlags instFlags);

  // find template scope corresp. to this var
  Scope *findParameterizingScope(Variable *bareQualifierVar,
                                 bool argsHaveVariables);
       
  // remove/restore scopes below 'bound'
  void removeScopesInside(ObjList<Scope> &dest, Scope *bound);
  void restoreScopesInside(ObjList<Scope> &src, Scope *bound);

  // merging template parameter lists from different declarations
  bool mergeParameterLists(Variable *prior,
                           SObjList<Variable> &destParams,
                           SObjList<Variable> const &srcParams);
  bool mergeTemplateInfos(Variable *prior, TemplateInfo *dest,
                          TemplateInfo const *src);

  // apply template arguments to make concrete types, or throw
  // xTypeDeduction to indicate failure
  Type *applyArgumentMapToType(MType &map, Type *origSrc);
  Type *applyArgumentMapToAtomicType
    (MType &map, AtomicType *origSrc, CVFlags srcCV);
  Type *applyArgumentMap_applyCV(CVFlags cv, Type *type);
  void applyArgumentMapToTemplateArgs
    (MType &map, ObjList<STemplateArgument> &dest,
                                 ObjList<STemplateArgument> const &srcArgs);
  STemplateArgument applyArgumentMapToExpression
    (MType &map, Expression *e);
  STemplateArgument applyArgumentMapToQualifiedName
    (MType &map, PQ_qualifier *qual);
  CompoundType *applyArgumentMap_instClass
    (MType &map, Variable *primary,
     ObjList<STemplateArgument> const &sargs);
  STemplateArgument applyArgumentMapToPQName
    (MType &map, Scope *scope, PQName *name);
  void applyArgumentMap_ensureComplete(CompoundType *ct);
  Type *applyArgumentMapToQualifiedType
    (MType &map, CompoundType *ct, PQName *name);

  // defined in notopt.cc
  Type *applyArgumentMapToType_helper(MType &map, Type *origSrc);

  // specialization support
  Variable *makeExplicitFunctionSpecialization
    (SourceLoc loc, DeclFlags dflags, PQName *name, FunctionType *ft);
  Variable *makeSpecializationVariable
    (SourceLoc loc, DeclFlags dflags, Variable *templ, FunctionType *type,
     SObjList<STemplateArgument> const &args);

  bool verifyCompatibleTemplateParameters(Scope *scope, CompoundType *prior);

  Variable *explicitFunctionInstantiation(PQName *name, Type *type,
                                          DeclFlags instFlags);

  Variable *findInstantiation(TemplateInfo *tinfo,
                              ObjList<STemplateArgument> const &sargs);
};


// when prepArgScopeForTemplCloneTcheck saves and restores scopes,
// it needs to remember the delegation pointers ....
class SavedScopePair {
public:      // data
  Scope *scope;                 // (nullable owner) main saved scope
  Scope *parameterizingScope;   // (nullable serf) delegation pointer

private:     // disallowed
  SavedScopePair(SavedScopePair&);
  void operator=(SavedScopePair&);

public:      // funcs
  SavedScopePair(Scope *s);     // delegation pointer set to NULL
  ~SavedScopePair();
};


// set/reset 'disambiguateOnly'
class DisambiguateOnlyTemp {
private:
  Env &env;       // relevant environment
  bool prev;      // previous value of 'disambiguateOnly'
  bool active;    // when false, we do nothing

public:
  DisambiguateOnlyTemp(Env &e, bool disOnly)
    : env(e),
      active(disOnly) {
    if (active) {
      prev = e.setDisambiguateOnly(true);
    }
  }

  ~DisambiguateOnlyTemp() {
    if (active) {
      env.setDisambiguateOnly(prev);
    }
  }
};


// isolate template instantiation from affecting other things that
// might be going on in the instantiation request context, in
// particular disambiguation
class InstantiationContextIsolator {
public:      // data
  Env &env;                    // tcheck env
  int origNestingLevel;        // original value of env.disambiguationNestingLevel
  bool origSecondPass;         // original value of env.secondPassTcheck
  ErrorList origErrors;        // errors extant before instantiation

private:     // disallowed
  InstantiationContextIsolator(InstantiationContextIsolator&);
  void operator=(InstantiationContextIsolator&);

public:      // funcs
  InstantiationContextIsolator(Env &env, SourceLoc loc);
  ~InstantiationContextIsolator();
};


// little hack to suppress errors in a given segment
class SuppressErrors {
private:
  Env &env;               // relevant environment
  ErrorList existing;     // errors before the operation

public:
  SuppressErrors(Env &e) : env(e) {
    // squirrel away the good messages
    existing.takeMessages(env.errors);
  }

  ~SuppressErrors() {
    // get rid of any messages added in the meantime
    env.errors.deleteAll();

    // put back the good ones
    env.errors.takeMessages(existing);
  }
};


// check default arguments during pass 2
class DefaultArgumentChecker : public ASTVisitor {
public:
  Env &env;
  bool isInstantiation;

public:
  DefaultArgumentChecker(Env &e, bool i)
    : env(e), isInstantiation(i) {}

  virtual bool visitIDeclarator(IDeclarator *obj);
  virtual bool visitTypeSpecifier(TypeSpecifier *obj);
};


// save env's error messages, then later restore them, as part of
// disambiguation activities
class DisambiguationErrorTrapper {
public:      // data
  Env &env;
  ErrorList existingErrors;       // saved messages

public:      // funcs
  DisambiguationErrorTrapper(Env &env);
  ~DisambiguationErrorTrapper();
};


// misc
bool isCopyConstructor(Variable const *funcVar, CompoundType *ct);
bool isCopyAssignOp(Variable const *funcVar, CompoundType *ct);
void addCompilerSuppliedDecls(Env &env, SourceLoc loc, CompoundType *ct);
bool equalOrIsomorphic(Type const *a, Type const *b);


#endif // CC_ENV_H
