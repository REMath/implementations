// cc_type.h            see license.txt for copyright and terms of use
// compile-type representation of C++ types
// see doc/cc_type.html
// and Diagram 1 of doc/cpp_er.html

// The original design intent was that type representation would be
// completely independent of the Expression language, or anything
// else from cc.ast.  That is, types should have meaning independent
// of the language of values, or of the syntax used to describe them
// in source code.
//
// However, the practicalities of parsing C++ have forced my hand in a
// couple of places.  Those places are marked with the annotation
// "(AST pointer)".  In all cases so far, I can forsee an intermediate
// transformation which would remove (e.g. nullify) all the AST
// pointers in the process of creating a "minimized" C++ subset.  In
// particular, it should be possible to translate away everything
// related to templates.
//
// *Please* do not add any additional AST pointers unless it is
// really necessary.  Also please make sure all the types can
// intelligbly print themselves *without* inspecting the AST pointers
// (by storing a textual representation if necessary).

#ifndef CC_TYPE_H
#define CC_TYPE_H

#include "str.h"          // string
#include "objlist.h"      // ObjList
#include "sobjlist.h"     // SObjList
#include "astlist.h"      // ASTList
#include "cc_flags.h"     // CVFlags, DeclFlags, SimpleTypeId
#include "strtable.h"     // StringRef
#include "strobjdict.h"   // StringObjDict
#include "cc_scope.h"     // Scope
#include "srcloc.h"       // SourceLoc
#include "exc.h"          // xBase
#include "serialno.h"     // INHERIT_SERIAL_BASE
#include "mflags.h"       // MatchFlags

class Variable;           // variable.h
class Env;                // cc_env.h
class TS_classSpec;       // cc.ast
class Expression;         // cc.ast
class TemplateArgument;   // cc.ast
class D_pointer;          // cc.ast
class D_reference;        // cc.ast
class D_func;             // cc.ast
class D_ptrToMember;      // cc.ast
class TypeSpecifier;      // cc.ast
class Declaration;        // cc.ast
class TypeVariable;       // template.h
class PseudoInstantiation;// template.h
class DependentQType;     // template.h
class ReadXML;            // xml.h
class MType;              // mtype.h

// fwd in this file
class AtomicType;
class SimpleType;
class NamedAtomicType;
class CompoundType;
class BaseClass;
class EnumType;
class CVAtomicType;
class PointerType;
class ReferenceType;
class FunctionType;
class ArrayType;
class PointerToMemberType;
class Type;
class TemplateInfo;
class STemplateArgument;
class TypeFactory;
class BasicTypeFactory;
class TypePred;


// FIX: is a debugging aid; remove
extern bool global_mayUseTypeAndVarToCString;


// --------------------- type visitor -----------------------        
// Visitor that digs down into template arguments, among other things.
// Like the AST visitors, the 'visit' functions return true to
// continue digging into subtrees, or false to prune the search.
class TypeVisitor {
public:
  virtual ~TypeVisitor() {}     // silence warning

  virtual bool visitType(Type *obj);
  virtual void postvisitType(Type *obj);

  virtual bool visitFunctionType_params(SObjList<Variable> &params);
  virtual void postvisitFunctionType_params(SObjList<Variable> &params);
  virtual bool visitFunctionType_params_item(Variable *param);
  virtual void postvisitFunctionType_params_item(Variable *param);

  virtual bool visitVariable(Variable *var);
  virtual void postvisitVariable(Variable *var);

  virtual bool visitAtomicType(AtomicType *obj);
  virtual void postvisitAtomicType(AtomicType *obj);

  // I don't know where to say this, so I'll say it here: there is no
  // call in EnumType::traverse() that will take you here; visitors
  // call it manually.  However, the existance of these methods allows
  // you to organize your code in the same way as you would for the
  // other classes.
  //
  // Also, please note that I cannot forward declare EnumType::Value,
  // so unless I move this class until after class Enum, I have to
  // make the argument type void!
  virtual bool visitEnumType_Value(void /*EnumType::Value*/ *obj);
  virtual void postvisitEnumType_Value(void /*EnumType::Value*/ *obj);

  virtual bool visitScope(Scope *obj);
  virtual void postvisitScope(Scope *obj);

  virtual bool visitScope_variables(StringRefMap<Variable> &variables);
  virtual void postvisitScope_variables(StringRefMap<Variable> &variables);
  virtual bool visitScope_variables_entry(StringRef name, Variable *var);
  virtual void postvisitScope_variables_entry(StringRef name, Variable *var);

  virtual bool visitScope_typeTags(StringRefMap<Variable> &typeTags);
  virtual void postvisitScope_typeTags(StringRefMap<Variable> &typeTags);
  virtual bool visitScope_typeTags_entry(StringRef name, Variable *var);
  virtual void postvisitScope_typeTags_entry(StringRef name, Variable *var);

  virtual bool visitScope_templateParams(SObjList<Variable> &templateParams);
  virtual void postvisitScope_templateParams(SObjList<Variable> &templateParams);
  virtual bool visitScope_templateParams_item(Variable *var);
  virtual void postvisitScope_templateParams_item(Variable *var);

  virtual bool visitBaseClass(BaseClass *bc);
  virtual void postvisitBaseClass(BaseClass *bc);

  virtual bool visitBaseClassSubobj(BaseClassSubobj *bc);
  virtual void postvisitBaseClassSubobj(BaseClassSubobj *bc);

  virtual bool visitBaseClassSubobj_parents(SObjList<BaseClassSubobj> &parents);
  virtual void postvisitBaseClassSubobj_parents(SObjList<BaseClassSubobj> &parents);
  virtual bool visitBaseClassSubobj_parents_item(BaseClassSubobj *parent);
  virtual void postvisitBaseClassSubobj_parents_item(BaseClassSubobj *parent);

  virtual bool visitSTemplateArgument(STemplateArgument *obj);
  virtual void postvisitSTemplateArgument(STemplateArgument *obj);

  virtual bool visitPseudoInstantiation_args(ObjList<STemplateArgument> &args);
  virtual void postvisitPseudoInstantiation_args(ObjList<STemplateArgument> &args);
  virtual bool visitPseudoInstantiation_args_item(STemplateArgument *arg);
  virtual void postvisitPseudoInstantiation_args_item(STemplateArgument *arg);

  virtual bool visitDependentQTypePQTArgsList(ObjList<STemplateArgument> &list);
  virtual void postvisitDependentQTypePQTArgsList(ObjList<STemplateArgument> &list);
  virtual bool visitDependentQTypePQTArgsList_item(STemplateArgument *sta);
  virtual void postvisitDependentQTypePQTArgsList_item(STemplateArgument *sta);

  // note that this call is always a leaf in the traversal; the type
  // visitor does *not* dig into Expressions (though of course you can
  // write a 'visitExpression' method that does)
  virtual bool visitExpression(Expression *obj);
  virtual void postvisitExpression(Expression *obj);
};


// --------------------- atomic types --------------------------
// interface to types that are atomic in the sense that no
// modifiers can be stripped away; see cc_type.html
class AtomicType {
public:     // types
  enum Tag {
    // these are defined in cc_type.h
    T_SIMPLE,                // int, char, float, etc.
    T_COMPOUND,              // struct/class/union
    T_ENUM,                  // enum

    // these are defined in template.h
    T_TYPEVAR,               // T
    T_PSEUDOINSTANTIATION,   // C<T>
    T_DEPENDENTQTYPE,        // C<T>::some_type

    NUM_TAGS
  };

public:     // funcs
  AtomicType();
  virtual ~AtomicType();

  virtual Tag getTag() const = 0;
  bool isSimpleType() const   { return getTag() == T_SIMPLE; }
  bool isCompoundType() const { return getTag() == T_COMPOUND; }
  bool isEnumType() const     { return getTag() == T_ENUM; }
  bool isTypeVariable() const { return getTag() == T_TYPEVAR; }
  bool isPseudoInstantiation() const { return getTag() == T_PSEUDOINSTANTIATION; }
  bool isDependentQType() const      { return getTag() == T_DEPENDENTQTYPE; }
  virtual bool isNamedAtomicType() const;    // default impl returns false

  // see smbase/macros.h
  DOWNCAST_FN(SimpleType)
  DOWNCAST_FN(NamedAtomicType)
  DOWNCAST_FN(CompoundType)
  DOWNCAST_FN(EnumType)
  DOWNCAST_FN(TypeVariable)
  DOWNCAST_FN(PseudoInstantiation)
  DOWNCAST_FN(DependentQType)

  // concrete types do not have holes
  bool isConcrete() const
    { return !isTypeVariable() && !isPseudoInstantiation(); }

  // this is type equality, *not* coercibility -- e.g. if
  // we say "extern type1 x" and then "extern type2 x" we
  // will allow it only if type1==type2
  bool equals(AtomicType const *obj) const;

  // print the string according to 'Type::printAsML'
  string toString() const;

  // print in C notation
  virtual string toCString() const = 0;

  // print in "ML" notation (really just more verbose)
  virtual string toMLString() const = 0;
  
  // size this type's representation occupies in memory; this
  // might throw XReprSize, see below
  virtual int reprSize() const = 0;

  // invoke 'vis.visitAtomicType(this)', and then traverse subtrees
  virtual void traverse(TypeVisitor &vis) = 0;

  // toString()+newline to cout
  void gdb() const;

  ALLOC_STATS_DECLARE
};


// represents one of C's built-in types;
// there are exactly as many of these objects as there are built-in types
class SimpleType : public AtomicType {
public:     // data
  SimpleTypeId const type;

  // global read-only array for each built-in type        
  // (read-only is enforced by making all of SimpleType's members
  // const, rather then the objects themselves, because doing the
  // latter would clash AtomicType pointers not being const below)
  static SimpleType fixed[NUM_SIMPLE_TYPES];

public:     // funcs
  SimpleType(SimpleTypeId t) : type(t) {}

  // AtomicType interface
  virtual Tag getTag() const { return T_SIMPLE; }
  virtual string toCString() const;
  virtual string toMLString() const;
  virtual int reprSize() const;
  virtual void traverse(TypeVisitor &vis);
};


// elements common to structs and enums
class NamedAtomicType : public AtomicType {
public:     // data
  StringRef name;          // (nullable) user-assigned name of this struct or enum
  Variable *typedefVar;    // (owner) implicit typedef variable
  AccessKeyword access;    // accessibility of this type in its declaration context

public:
  NamedAtomicType(StringRef name);
  ~NamedAtomicType();

  virtual bool isNamedAtomicType() const;       // returns true
};


// represent a base class
class BaseClass {
public:
  CompoundType *ct;          // (serf) the base class itself
  AccessKeyword access;      // access mode of the inheritance
  bool isVirtual;            // true for virtual inheritance

public:
  BaseClass(BaseClass const &obj)
    : DMEMB(ct), DMEMB(access), DMEMB(isVirtual) {}
  BaseClass(CompoundType *c, AccessKeyword a, bool v)
    : ct(c), access(a), isVirtual(v) {}
    
  // this isn't virtual because the caller always knows the
  // dynamic type
  void traverse(TypeVisitor &vis);
};

// represent an instance of a base class in a particular class'
// inheritance hierarchy; it is these things that represent things
// like diamond inheritance patterns; the terminology comes from
// [cppstd 10.1 para 4]
class BaseClassSubobj : public BaseClass {
public:
  // classes that this one inherits from; non-owning since the
  // 'parents' links form a DAG, not a tree; in fact I regard
  // this list as an owner of exactly those sub-objects whose
  // inheritance is *not* virtual
  SObjList<BaseClassSubobj> parents;

  // for visit-once-only traversals
  mutable bool visited;

public:
  BaseClassSubobj(CompoundType *c, AccessKeyword a, bool v)
    : BaseClass(c, a, v)
  {}
  BaseClassSubobj(BaseClass const &base);
  ~BaseClassSubobj();
  // dsw: note: we use the implicit operator=() on this object

  // name and virtual address to uniquely identify this object
  string canonName() const;

  void traverse(TypeVisitor &vis);
};

// represent a user-defined compound type; the members of the
// compound are whatever has been entered in the Scope
class CompoundType : public NamedAtomicType, public Scope {
public:      // types
  // NOTE: keep these consistent with TypeIntr (in file cc_flags.h)
  enum Keyword { K_STRUCT, K_CLASS, K_UNION, NUM_KEYWORDS };

public:      // data
  bool forward;               // true when it's only fwd-declared
  Keyword keyword;            // keyword used to introduce the type

  // nonstatic data members, in the order they appear within the body
  // of the class definition; note that this is partially redundant
  // with the Scope's 'variables' map, and hence should not be changed
  // without also updating that map
  SObjList<Variable> dataMembers;

  // nonstatic function members, in the order they appear within the
  // body of the class definition.
  SObjList<Variable> functionMembers;

  // whether this type has the builtin default ctor, copy ctor,
  // destructor and assign operator, as there is no such user-defined
  // function. these bits are unset if there is no user-defined function,
  // but there is a struct member with such a function.
  bool hasBuiltinDefaultCtor;
  bool hasBuiltinCopyCtor;
  bool hasBuiltinDtor;
  bool hasBuiltinAssign;

  // classes from which this one inherits; 'const' so you have to
  // use 'addBaseClass', but public to make traversal easy
  const ObjList<BaseClass> bases;

  // collected virtual base class subobjects
  ObjList<BaseClassSubobj> virtualBases;

  // this is the root of the subobject hierarchy diagram
  // invariant: subobj.ct == this
  BaseClassSubobj subobj;

  // list of all conversion operators this class has, including
  // those that have been inherited but not then hidden
  SObjList<Variable> conversionOperators;
  
  // list of friends; the friends are members of other scopes, but
  // they can access protected/private members of this class, and
  // argument-dependent lookups in this class can find them
  //
  // this is almost certainly *not* the best way to record this
  // information if access control were to be implemented, but it
  // does the job for the moment
  SObjList<Variable> friends;

  // if this class is a template instantiation, 'instName' is
  // the class name plus a rendering of the arguments; otherwise
  // it's the same as 'name'; this is for debugging
  StringRef instName;

  // AST node that describes this class; used for implementing
  // templates (AST pointer)
  // dsw: used for other purposes also
  TS_classSpec *syntax;               // (nullable serf)

  // template parameter scope that is consulted for lookups after
  // this scope and its base classes; this changes over time as
  // the class is added to and removed from the scope stack; it
  // is NULL whenever it is not on the scope stack
  Scope *parameterizingScope;         // (nullable serf)

  // this is the type of the compound as bound to the
  // injected-class-name; it is different than typedefVar->type
  // for template classes, as the former is the template class
  // itself while the latter is a PseudoInstantiation thereof
  Type *selfType;                     // (nullable serf)

private:     // funcs
  void makeSubobjHierarchy(BaseClassSubobj *subobj, BaseClass const *newBase);

  BaseClassSubobj const *findVirtualSubobjectC(CompoundType const *ct) const;
  BaseClassSubobj *findVirtualSubobject(CompoundType *ct)
    { return const_cast<BaseClassSubobj*>(findVirtualSubobjectC(ct)); }

  static void clearVisited_helper(BaseClassSubobj const *subobj);

  static void getSubobjects_helper
    (SObjList<BaseClassSubobj const> &dest, BaseClassSubobj const *subobj);

  void addLocalConversionOp(Variable *op);

protected:   // funcs
  // create an incomplete (forward-declared) compound
  // experiment: force creation of these to go through the factory too
  CompoundType(Keyword keyword, StringRef name);
  friend class TypeFactory;
  friend class TypeXmlReader;
  
  // override no-op implementation in Scope
  virtual void afterAddVariable(Variable *v);

public:      // funcs
  virtual ~CompoundType();

  bool isComplete() const { return !forward; }
  
  // true if this is a class that is incomplete because it requires
  // template arguments to be supplied (i.e. not true for classes
  // that come from templates, but all arguments have been supplied)
  bool isTemplate(bool considerInherited = false) const;
  
  // true if it is an instance (fully concrete type arguments) of some
  // template
  bool isInstantiation() const;

  // manipulate 'templateInfo', which is now stored in the 'typedefVar'
  TemplateInfo *templateInfo() const;
  void setTemplateInfo(TemplateInfo *templInfo0);

  // same as 'typedefVar' but with a bunch of assertions...
  Variable *getTypedefVar() const;

  // true if the class has RTTI/vtable
  bool hasVirtualFns() const;

  static char const *keywordName(Keyword k);

  // AtomicType interface
  virtual Tag getTag() const { return T_COMPOUND; }
  virtual string toCString() const;
  virtual string toMLString() const;
  virtual int reprSize() const;
  virtual void traverse(TypeVisitor &vis);

  string toStringWithFields() const;
  string keywordAndName() const { return toCString(); }

  int numFields() const;

  // returns NULL if doesn't exist
  Variable *getNamedField(StringRef name, Env &env, LookupFlags f=LF_NONE)
    { return lookupVariable(name, env, f); }

  // alias for Scope::addVariable (should probably be deleted)
  void addField(Variable *v);

  // sm: for compatibility with existing code
  SObjList<Variable> &getDataVariablesInOrder() 
    { return dataMembers; }

  // return the ordinal position of the named nonstatic data field
  // in this class, starting with 0; or, return -1 if the field does
  // not exist (this is a query on 'dataMembers')
  int getDataMemberPosition(StringRef name) const;

  // add to 'bases'; incrementally maintains 'virtualBases'
  virtual void addBaseClass(BaseClass * /*owner*/ newBase);

  // true if this class inherits from 'ct', either directly or
  // indirectly, and the inheritance is virtual
  bool hasVirtualBase(CompoundType const *ct) const
    { return !!findVirtualSubobjectC(ct); }

  // set all the 'visited' fields to false in the subobject hierarchy
  void clearSubobjVisited() const;

  // collect all of the subobjects into a list; each subobject
  // appears exactly once; NOTE: you may want to call 
  // Env::ensureClassBodyInstantiated before calling this, since
  // an uninstantiated class won't have any subobjects yet
  void getSubobjects(SObjList<BaseClassSubobj const> &dest) const;

  // render the subobject hierarchy to a 'dot' graph
  string renderSubobjHierarchy() const;

  // how many times does 'ct' appear as a subobject?
  // returns 1 if ct==this
  int countBaseClassSubobjects(CompoundType const *ct) const;

  bool hasUnambiguousBaseClass(CompoundType const *ct) const
    { return countBaseClassSubobjects(ct)==1; }
  bool hasBaseClass(CompoundType const *ct) const
    { return countBaseClassSubobjects(ct)>=1; }
  bool hasStrictBaseClass(CompoundType const *ct) const
    { return this != ct && hasBaseClass(ct); }

  // compute the least upper bound of two compounds in the inheritance
  // network; 'wasAmbig==true' means that the intersection of the
  // superclasses was not empty, but that set had no least element;
  // return NULL if no LUB ("least" means most-derived)
  static CompoundType *lub(CompoundType *t1, CompoundType *t2, bool &wasAmbig);

  // call this when we're finished adding base classes and member
  // fields; it builds 'conversionOperators'; 'specialName' is the
  // name under which the conversion operators have been filed in
  // the class scope
  virtual void finishedClassDefinition(StringRef specialName);
  
  // true if this is an "aggregate" (8.5.1p1)
  bool isAggregate() const;
};

string toString(CompoundType::Keyword k);


// represent an enumerated type
class EnumType : public NamedAtomicType {
public:     // types
  // represent a single value in an enum
  class Value {
  public:
    StringRef name;           // the thing whose name is being defined
    EnumType *type;           // enum in which it was declared
    int value;                // value it's assigned to

    // similar to fields, I keep a record of where this came from
    Variable *decl;           // (nullable serf)

  public:
    Value(StringRef n, EnumType *t, int v, Variable *d);
    ~Value();
  };

public:     // data
  StringObjDict<Value> valueIndex;    // values in this enumeration
  int nextValue;                      // next value to assign to elements automatically

public:     // funcs
  EnumType(StringRef n) : NamedAtomicType(n), nextValue(0) {}
  ~EnumType();

  // AtomicType interface
  virtual Tag getTag() const { return T_ENUM; }
  virtual string toCString() const;
  virtual string toMLString() const;
  virtual int reprSize() const;
  virtual void traverse(TypeVisitor &vis);

  Value *addValue(StringRef name, int value, /*nullable*/ Variable *d);
  Value const *getValue(StringRef name) const;
};


// moved PseudoInstantiation into template.h


// ---------------------- TypePred ----------------------------
// This visitor predates TypeVisitor, and is a little different
// because it does not dig into atomic types or template args.
// It would be good to merge them at some point.

// abstract superclass
class TypePred {
public:
  virtual bool operator() (Type const *t) = 0;
  virtual ~TypePred() {}     // gcc sux
};

// when you just want a stateless predicate
typedef bool (*TypePredFunc)(Type const *t);

class StatelessTypePred : public TypePred {
  TypePredFunc const f;
public:
  StatelessTypePred(TypePredFunc f0) : f(f0) {}
  virtual bool operator() (Type const *t);
};


// ------------------- constructed types -------------------------
// generic constructed type; to allow client analyses to annotate the
// description of types, this class is inherited by "Type", the class
// that all of the rest of the parser regards as being a "type"
//
// note: clients should refer to Type, not BaseType
class BaseType INHERIT_SERIAL_BASE {
public:     // types
  enum Tag {
    // dsw: I want these to not be picked arbitrarily by the compiler,
    // so I start it at something specific; I like 0 to be meaningless
    // so that nothing meaningfull happens by default, a la pointers.
    T_ATOMIC = 1,               // int const, class Foo, etc.
    T_POINTER,                  // int *
    T_REFERENCE,                // int &
    T_FUNCTION,                 // int ()(int, float)
    T_ARRAY,                    // int [3]
    T_POINTERTOMEMBER,          // int C::*

    T_LAST_TYPE_TAG,
    // IMPORTANT: it is important that T_LAST_TYPE_TAG be the last one
    // so I can make a disjoint set in Oink by starting my enum at
    // T_LAST_TYPE_TAG+1.  Therefore if you add anything, add it
    // before T_LAST_TYPE_TAG.
  };

public:     // data
  // when true (the default is false), types are printed in ML-like
  // notation instead of C notation by AtomicType::toString and
  // Type::toString
  static bool printAsML;

private:    // disallowed
  BaseType(BaseType&);

private:    // funcs
  // the constructor of BaseType is private so the only subclass
  // is Type, an assumption relied upon in BaseType::equals
  BaseType();
  friend class Type;

public:     // funcs
  virtual ~BaseType();

  virtual Tag getTag() const = 0;
  bool isCVAtomicType() const { return getTag() == T_ATOMIC; }
  bool isPointerType() const { return getTag() == T_POINTER; }
  bool isReferenceType() const { return getTag() == T_REFERENCE; }
  bool isFunctionType() const { return getTag() == T_FUNCTION; }
  bool isArrayType() const { return getTag() == T_ARRAY; }
  bool isPointerToMemberType() const { return getTag() == T_POINTERTOMEMBER; }

  DOWNCAST_FN(CVAtomicType)
  DOWNCAST_FN(PointerType)
  DOWNCAST_FN(ReferenceType)
  DOWNCAST_FN(FunctionType)
  DOWNCAST_FN(ArrayType)
  DOWNCAST_FN(PointerToMemberType)

  // like above, this is (structural) equality, not coercibility;
  // internally, this calls the innerEquals() method on the two
  // objects, once their tags have been established to be equal
  bool equals(BaseType const *obj, MatchFlags flags = MF_NONE) const;

  // compute a hash value: equal types (EF_EXACT) have the same hash
  // value, and unequal types are likely to have different values
  unsigned hashValue() const;
  virtual unsigned innerHashValue() const = 0;

  // print the string according to 'printAsML'
  string toString() const;

  // print the type, with an optional name like it was a declaration
  // for a variable of that type
  string toCString() const;
  string toCString(char const * /*nullable*/ name) const;
  string toCString(rostring name) const { return toCString(name.c_str()); }

  // NOTE: yes, toMLString() is virtual, whereas toCString() is not
  virtual string toMLString() const = 0;
  void putSerialNo(stringBuilder &sb) const;
  
  // toString+newline to cout
  void gdb() const;

  // the left/right business is to allow us to print function
  // and array types in C's syntax; if 'innerParen' is true then
  // the topmost type constructor should print the inner set of
  // paretheses
  virtual string leftString(bool innerParen=true) const = 0;
  virtual string rightString(bool innerParen=true) const;    // default: returns ""

  // size of representation at run-time; for now uses nominal 32-bit
  // values
  virtual int reprSize() const = 0;

  // filter on all constructed types that appear in the type,
  // *including* parameter types; return true if any constructor
  // satisfies 'pred' (note that recursive types always go through
  // CompoundType, and this does not dig into the fields of
  // CompoundTypes)
  virtual bool anyCtorSatisfies(TypePred &pred) const=0;

  // automatically wrap 'pred' in a StatelessTypePred;
  // trailing 'F' in name means "function", so as to avoid
  // overloading and overriding on the same name
  bool anyCtorSatisfiesF(TypePredFunc f) const;

  // return the cv flags that apply to this type, if any;
  // default returns CV_NONE
  virtual CVFlags getCVFlags() const;
  bool isConst() const { return !!(getCVFlags() & CV_CONST); }

  // invoke 'vis.visitType(this)', and then traverse subtrees
  virtual void traverse(TypeVisitor &vis) = 0;

  // some common queries
  bool isSimpleType() const;
  SimpleType const *asSimpleTypeC() const;
  bool isSimple(SimpleTypeId id) const;
  bool isSimpleCharType() const { return isSimple(ST_CHAR); }
  bool isSimpleWChar_tType() const { return isSimple(ST_WCHAR_T); }
  bool isStringType() const;
  bool isIntegerType() const;            // any of the simple integer types
  bool isEnumType() const;
  bool isUnionType() const { return isCompoundTypeOf(CompoundType::K_UNION); }
  bool isStructType() const { return isCompoundTypeOf(CompoundType::K_STRUCT); }
  bool isCompoundTypeOf(CompoundType::Keyword keyword) const;
  bool isVoid() const { return isSimple(ST_VOID); }
  bool isBool() const { return isSimple(ST_BOOL); }
  bool isEllipsis() const { return isSimple(ST_ELLIPSIS); }
  bool isError() const { return isSimple(ST_ERROR); }
  bool isDependent() const;    // TODO: this should be ST_DEPENDENT only
  bool isOwnerPtr() const;
  bool isMethod() const;                       // function and method

  // ST_DEPENDENT or TypeVariable or PseudoInstantiation or DependentQType
  bool isGeneralizedDependent() const;
  bool containsGeneralizedDependent() const;   // anywhere in Type tree

  // (some of the following are redundant but I want them anyway, to
  // continue with the pattern that isXXX is for language concepts and
  // isXXXType is for implementation concepts)

  // pointer/reference stuff
  bool isPointer() const { return isPointerType(); }
  bool isReference() const { return isReferenceType(); }
  bool isReferenceToConst() const;
  bool isLval() const { return isReference(); }// C terminology

  // allow some degree of unified handling of PointerType and ReferenceType
  bool isPtrOrRef() const { return isPointer() || isReference(); }
  bool isPointerOrArrayRValueType() const;

  // dsw: this is virtual because in Oink an int can act as a pointer
  // so I need a way to do that
  virtual Type *getAtType() const;

  // note that Type overrides these to return Type instead of BaseType
  BaseType const *asRvalC() const;             // if I am a reference, return referrent type
  BaseType *asRval() { return const_cast<BaseType*>(asRvalC()); }

  bool isCVAtomicType(AtomicType::Tag tag) const;
  bool isTypeVariable() const { return isCVAtomicType(AtomicType::T_TYPEVAR); }
  TypeVariable const *asTypeVariableC() const;
  TypeVariable *asTypeVariable()
    { return const_cast<TypeVariable*>(asTypeVariableC()); }

  // downcast etc. to NamedAtomicType
  bool isNamedAtomicType() const;
  NamedAtomicType *ifNamedAtomicType();  // NULL or corresp. NamedAtomicType
  NamedAtomicType const *asNamedAtomicTypeC() const;
  NamedAtomicType *asNamedAtomicType() { return const_cast<NamedAtomicType*>(asNamedAtomicTypeC()); }

  // similar for CompoundType
  bool isCompoundType() const { return isCVAtomicType(AtomicType::T_COMPOUND); }
  CompoundType *ifCompoundType();        // NULL or corresp. compound
  CompoundType const *asCompoundTypeC() const; // fail assertion if not
  CompoundType *asCompoundType() { return const_cast<CompoundType*>(asCompoundTypeC()); }

  // etc. ...
  bool isPseudoInstantiation() const { return isCVAtomicType(AtomicType::T_PSEUDOINSTANTIATION); }
  PseudoInstantiation const *asPseudoInstantiationC() const;
  PseudoInstantiation *asPseudoInstantiation() { return const_cast<PseudoInstantiation*>(asPseudoInstantiationC()); }

  bool isDependentQType() const { return isCVAtomicType(AtomicType::T_DEPENDENTQTYPE); }

  // something that behaves like a CompoundType in most respects
  bool isLikeCompoundType() const
    { return isCompoundType() || isPseudoInstantiation(); }

  // this is true if any of the type *constructors* on this type
  // refer to ST_ERROR; we don't dig down inside e.g. members of
  // referred-to classes
  bool containsErrors() const;

  // similar for TypeVariable
  bool containsTypeVariables() const;

  // returns true if contains type or object variables (template
  // parameters); recurses down into TemplateArguments
  //
  // if 'map' is not NULL, then we only count variables that
  // are *not* bound in 'map'
  bool containsVariables(MType *map = NULL) const;

  ALLOC_STATS_DECLARE
};

string cvToString(CVFlags cv);

#ifdef TYPE_CLASS_FILE
  // pull in the definition of Type, which may have additional
  // fields (etc.) added for the client analysis
  #include TYPE_CLASS_FILE
#else
  // please see cc_type.html, section 6, "BaseType and Type", for more
  // information about this class
  class Type : public BaseType {
  protected:   // funcs
    Type() {}

  public:      // funcs
    // do not leak the name "BaseType"
    Type const *asRvalC() const
      { return static_cast<Type const *>(BaseType::asRvalC()); }
    Type *asRval()
      { return static_cast<Type*>(BaseType::asRval()); }
  };
#endif // TYPE_CLASS_FILE

// supports the use of 'Type*' in AST constructor argument lists
string toString(Type *t);


// essentially just a wrapper around an atomic type, but
// also with optional const/volatile flags
class CVAtomicType : public Type {
public:     // data
  AtomicType *atomic;          // (serf) underlying type
  CVFlags cv;                  // const/volatile

protected:
  friend class BasicTypeFactory;
  friend class TypeXmlReader;
  CVAtomicType(AtomicType *a, CVFlags c)
    : atomic(a), cv(c) {}

  // need this to make a static array of them
  CVAtomicType(CVAtomicType const &obj)
    : atomic(obj.atomic), cv(obj.cv) {}

public:
  bool isConst() const { return !!(cv & CV_CONST); }
  bool isVolatile() const { return !!(cv & CV_VOLATILE); }

  // Type interface
  virtual Tag getTag() const { return T_ATOMIC; }
  unsigned innerHashValue() const;
  virtual string toMLString() const;
  virtual string leftString(bool innerParen=true) const;
  virtual int reprSize() const;
  virtual bool anyCtorSatisfies(TypePred &pred) const;
  virtual CVFlags getCVFlags() const;
  virtual void traverse(TypeVisitor &vis);
};

             
// type of a pointer
class PointerType : public Type {
public:     // data
  CVFlags cv;                  // const/volatile; refers to pointer *itself*
  Type *atType;                // (serf) type of thing pointed-at

protected:  // funcs
  friend class BasicTypeFactory;
  friend class TypeXmlReader;
  PointerType(CVFlags c, Type *a);

public:
  bool isConst() const { return !!(cv & CV_CONST); }
  bool isVolatile() const { return !!(cv & CV_VOLATILE); }

  // Type interface
  virtual Tag getTag() const { return T_POINTER; }
  unsigned innerHashValue() const;
  virtual string toMLString() const;
  virtual string leftString(bool innerParen=true) const;
  virtual string rightString(bool innerParen=true) const;
  virtual int reprSize() const;
  virtual bool anyCtorSatisfies(TypePred &pred) const;
  virtual CVFlags getCVFlags() const;
  virtual void traverse(TypeVisitor &vis);
};


// type of a reference
class ReferenceType : public Type {
public:     // data
  Type *atType;                // (serf) type of thing pointed-at

protected:  // funcs
  friend class BasicTypeFactory;
  friend class TypeXmlReader;
  ReferenceType(Type *a);

public:
  bool isConst() const { return false; }
  bool isVolatile() const { return false; }

  // Type interface
  virtual Tag getTag() const { return T_REFERENCE; }
  unsigned innerHashValue() const;
  virtual string toMLString() const;
  virtual string leftString(bool innerParen=true) const;
  virtual string rightString(bool innerParen=true) const;
  virtual int reprSize() const;
  virtual bool anyCtorSatisfies(TypePred &pred) const;
  virtual CVFlags getCVFlags() const;
  virtual void traverse(TypeVisitor &vis);
};


// some flags that can be associated with function types
enum FunctionFlags {
  FF_NONE          = 0x0000,  // nothing special
  FF_METHOD        = 0x0001,  // function is a nonstatic method
  FF_VARARGS       = 0x0002,  // accepts variable # of arguments
  FF_CONVERSION    = 0x0004,  // conversion operator function
  FF_CTOR          = 0x0008,  // constructor
  FF_DTOR          = 0x0010,  // destructor
  FF_BUILTINOP     = 0x0020,  // built-in operator function (cppstd 13.6)
  FF_NO_PARAM_INFO = 0x0040,  // C parameter list "()" (C99 6.7.5.3 para 14)
  FF_DEFAULT_ALLOC = 0x0080,  // is a default [de]alloc function from 3.7.3p2
  FF_KANDR_DEFN    = 0x0100,  // derived from a K&R-style function definition
  FF_ALL           = 0x01FF,  // all flags set to 1
};
ENUM_BITWISE_OPS(FunctionFlags, FF_ALL);


// type of a function
class FunctionType : public Type {
public:     // types
  // list of exception types that can be thrown
  class ExnSpec {
  public:
    SObjList<Type> types;

  public:
    ExnSpec() {}
    ExnSpec(ExnSpec const &obj);
    ~ExnSpec();

    bool anyCtorSatisfies(TypePred &pred) const;
  };

public:     // data
  // various boolean properties
  FunctionFlags flags;

  // type of return value
  Type *retType;                     // (serf)

  // list of function parameters; if (flags & FF_METHOD) then the
  // first parameter is '__receiver'
  SObjList<Variable> params;

  // allowable exceptions, if not NULL
  ExnSpec *exnSpec;                  // (nullable owner)

protected:  // funcs
  friend class BasicTypeFactory;
  friend class TypeXmlReader;

  FunctionType(Type *retType);

public:
  virtual ~FunctionType();

  // interpretations of flags
  bool hasFlag(FunctionFlags f) const { return !!(flags & f); }
  bool isMethod() const               { return hasFlag(FF_METHOD); }
  bool acceptsVarargs() const         { return hasFlag(FF_VARARGS); }
  bool isConversionOperator() const   { return hasFlag(FF_CONVERSION); }
  bool isConstructor() const          { return hasFlag(FF_CTOR); }
  bool isDestructor() const           { return hasFlag(FF_DTOR); }
  
  void setFlag(FunctionFlags f)       { flags |= f; }
  void clearFlag(FunctionFlags f)     { flags &= ~f; }

  // if the '__receiver' parameter (if any) is ignored in both
  // function types, am I equal to 'obj'?
  bool equalOmittingReceiver(FunctionType const *obj) const
    { return equals(obj, MF_STAT_EQ_NONSTAT | MF_IGNORE_IMPLICIT); }
                                             
  // true if all parameters after 'startParam' (0 is first) have
  // default values      
  bool paramsHaveDefaultsPast(int startParam) const;

  // append a parameter to the (ordinary) parameters list
  void addParam(Variable *param);

  // add the implicit '__receiver' param; sets 'isMember()' to true
  void addReceiver(Variable *param);

  // Note: After calling 'addParam', etc., the client must call
  // TypeFactory::doneParams so that the factory has a chance to
  // do any final adjustments.

  Variable const *getReceiverC() const;  // 'isMember' must be true
  Variable *getReceiver() { return const_cast<Variable*>(getReceiverC()); }

  CVFlags getReceiverCV() const;         // dig down; or CV_NONE if !isMember
  CompoundType *getClassOfMember();      // 'isMember' must be true
  
  // the above only works if the function is a member of a concrete
  // class; if it's a member of a template class, this must be used
  NamedAtomicType *getNATOfMember();

  // more specialized printing, for Cqual++ syntax
  static string rightStringQualifiers(CVFlags cv);
  virtual string rightStringUpToQualifiers(bool innerParen) const;
  virtual string rightStringAfterQualifiers() const;

  // print the function type, but use these cv-flags as the
  // receiver param cv-flags
  string toString_withCV(CVFlags cv) const;

  // a hook for the verifier's printer
  virtual void extraRightmostSyntax(stringBuilder &sb) const;

  // Type interface
  virtual Tag getTag() const { return T_FUNCTION; }
  unsigned innerHashValue() const;
  virtual string toMLString() const;
  virtual string leftString(bool innerParen=true) const;
  virtual string rightString(bool innerParen=true) const;
  virtual int reprSize() const;
  virtual bool anyCtorSatisfies(TypePred &pred) const;
  virtual void traverse(TypeVisitor &vis);
};


// type of an array
class ArrayType : public Type {
public:       // types
  enum { 
    NO_SIZE = -1,              // no size specified
    DYN_SIZE = -2,             // GNU extension: size is not a constant
    DEP_SIZE = -3              // size is dependent
  };

public:       // data
  Type *eltType;               // (serf) type of the elements
  int size;                    // specified size (>=0), or NO_SIZE or DYN_SIZE
  TypeVariable *depType;       // variable for DEPENDENT_SIZE, if available

  // Note that whether a size of 0 is legal depends on the current
  // language settings (cc_lang.h), so most code should adapt itself
  // to that possibility.

private:      // funcs
  void checkWellFormedness() const;

protected:
  friend class BasicTypeFactory;
  friend class TypeXmlReader;
  ArrayType(Type *e, int s = NO_SIZE)
    : eltType(e), size(s), depType(NULL) { checkWellFormedness(); }
  ArrayType(ReadXML&)           // a ctor for de-serialization
    : eltType(NULL), size(NO_SIZE), depType(NULL) {}

public:
  int getSize() const { return size; }
  bool hasSize() const { return size >= 0; }

  // Type interface
  virtual Tag getTag() const { return T_ARRAY; }
  unsigned innerHashValue() const;
  virtual string toMLString() const;
  virtual string leftString(bool innerParen=true) const;
  virtual string rightString(bool innerParen=true) const;
  virtual int reprSize() const;
  virtual bool anyCtorSatisfies(TypePred &pred) const;
  virtual void traverse(TypeVisitor &vis);
};


// pointer to member
class PointerToMemberType : public Type {
public:
  // Usually, this is a compound type, as ptr-to-members are
  // w.r.t. some compound.  However, to support the 'compound'
  // being a template parameter, we generalize slightly so that
  // a TypeVariable can be the 'inClass'.
  NamedAtomicType *inClassNAT;

  CVFlags cv;                   // whether this pointer is const
  Type *atType;                 // type of the member

protected:
  friend class BasicTypeFactory;
  friend class TypeXmlReader;
  PointerToMemberType(NamedAtomicType *inClassNAT0, CVFlags c, Type *a);
  PointerToMemberType(ReadXML&) // a ctor for de-serialization
    : inClassNAT(NULL), cv(CV_NONE), atType(NULL) {}

public:
  bool isConst() const { return !!(cv & CV_CONST); }

  // use this in contexts where the 'inClass' is known to be
  // a real compound (which is most contexts); this fails an
  // assertion if it turns out to be a TypeVariable
  CompoundType *inClass() const;

  // Type interface
  virtual Tag getTag() const { return T_POINTERTOMEMBER; }
  unsigned innerHashValue() const;
  virtual string toMLString() const;
  virtual string leftString(bool innerParen=true) const;
  virtual string rightString(bool innerParen=true) const;
  virtual int reprSize() const;
  virtual bool anyCtorSatisfies(TypePred &pred) const;
  virtual CVFlags getCVFlags() const;
  virtual void traverse(TypeVisitor &vis);
};


// moved into template.h:
//   class TypeVariable
//   class TemplateParams
//   class InheritedTemplateParams
//   class TemplateInfo
//   class STemplateArgument


// ------------------- type factory -------------------
// The type factory is used for constructing objects that represent
// C++ types.  The reasons for using a factory instead of direct
// construction include:
//
//   - Types have a complicated and unpredictable sharing structure,
//     which makes recursive deallocation impossible.  The factory
//     is thus given responsibility for deallocation of all objects
//     created by that factory.  (Hmm.. currently there's no interface
//     for relinquishing a reference back to the factory... doh.)
//
//   - Types are intended to be immutable, and thus referentially
//     transparent.  This enables the optimization of "hash consing"
//     where multiple requests for the same equivalent object yield
//     the exact same object.  The factory is responsible for
//     maintaining the data structures necessary for this, and for
//     choosing whether to do it at all.
//
//   - It is often desirable to annotate Types, but the base Type
//     hierarchy should be free from any particular annotations.
//     The factory allows one to derive subclasses of Type to add
//     such annotations, without modifying creation sites (since
//     they use the factory).  Of course, an alternative is to use
//     a hash table on the side, but that's sometimes inconvenient.

// first, we have the abstract interface of a TypeFactory
class TypeFactory {
public:
  virtual ~TypeFactory() {}      // silence stupid compiler warnings

  // ---- constructors for the atomic types ----
  // for now, only CompoundType is built this way, and I'm going to
  // provide a default implementation in TypeFactory to avoid having
  // to change the interface w.r.t. cc_qual
  virtual CompoundType *makeCompoundType
    (CompoundType::Keyword keyword, StringRef name);

  // ---- constructors for the constructed types ----
  virtual CVAtomicType *makeCVAtomicType(AtomicType *atomic, CVFlags cv)=0;

  virtual PointerType *makePointerType(CVFlags cv, Type *atType)=0;

  // this returns a Type* instead of a ReferenceType because I need to
  // be able to return an error type
  virtual Type *makeReferenceType(Type *atType)=0;

  virtual FunctionType *makeFunctionType(Type *retType)=0;

  // this must be called after 'makeFunctionType', once all of the
  // parameters have been added
  virtual void doneParams(FunctionType *ft)=0;

  virtual ArrayType *makeArrayType(Type *eltType, int size)=0;

  virtual PointerToMemberType *makePointerToMemberType
    (NamedAtomicType *inClassNAT, CVFlags cv, Type *atType)=0;


  // ---- create a type based on another one ----
  // NOTE: all 'syntax' pointers are nullable, since there are contexts
  // where I don't have an AST node to pass

  // NOTE: The functions in this section do *not* modify their argument
  // Types, rather they return a new object if the desired Type is different
  // from the one passed-in.  (That is, they behave functionally.)

  // do a shallow clone
  virtual Type *shallowCloneType(Type *baseType);

  // given a type, set its cv-qualifiers to 'cv'; return NULL if the
  // base type cannot be so qualified; I pass the syntax from which
  // the 'cv' flags were derived, when I have it, for the benefit of
  // extension analyses
  //
  // NOTE: 'baseType' is *not* modified; a copy is returned if necessary
  virtual Type *setQualifiers(SourceLoc loc, CVFlags cv, Type *baseType,
                                TypeSpecifier * /*nullable*/ syntax);

  // add 'cv' to existing qualifiers; default implementation just
  // calls setQualifiers
  virtual Type *applyCVToType(SourceLoc loc, CVFlags cv, Type *baseType,
                              TypeSpecifier * /*nullable*/ syntax);

  // build a pointer type from a syntactic description; here I allow
  // the factory to know the name of an AST node, but the default
  // implementation will not use it, so it need not be linked in for
  // this to make sense
  virtual Type *syntaxPointerType(SourceLoc loc,
    CVFlags cv, Type *underlying, D_pointer * /*nullable*/ syntax);
  virtual Type *syntaxReferenceType(SourceLoc loc,
    Type *underlying, D_reference * /*nullable*/ syntax);

  // similar for a function type; the parameters will be added by
  // the caller after this function returns
  virtual FunctionType *syntaxFunctionType(SourceLoc loc,
    Type *retType, D_func * /*nullable*/ syntax, TranslationUnit *tunit);

  // and another for pointer-to-member
  virtual PointerToMemberType *syntaxPointerToMemberType(SourceLoc loc,
    NamedAtomicType *inClassNAT, CVFlags cv, Type *atType,
    D_ptrToMember * /*nullable*/ syntax);

  // given a class, build the type of the receiver object parameter
  // 1/19/03: it should be a *reference* type
  // 1/30/04: fixing name: it's the receiver, not 'this'
  // 4/18/04: the 'classType' has been generalized because we
  //          represent ptr-to-member-func using a FunctionType
  //          with receiver parameter of type 'classType'
  virtual Type *makeTypeOf_receiver(SourceLoc loc,
    NamedAtomicType *classType, CVFlags cv, D_func * /*nullable*/ syntax);

  // given a function type and a return type, make a new function type
  // which is like it but has no parameters; i.e., copy all fields
  // except 'params'; this does *not* call doneParams
  virtual FunctionType *makeSimilarFunctionType(SourceLoc loc,
    Type *retType, FunctionType *similar);

  // ---- similar functions for Variable ----
  // Why not make a separate factory?
  //   - It's inconvenient to have two.
  //   - Every application I can think of will want to define both
  //     or neither.
  //   - Variable is used by Type and vice-versa.. they could have
  //     both been defined in cc_type.h
  virtual Variable *makeVariable(SourceLoc L, StringRef n,
                                 Type *t, DeclFlags f, TranslationUnit *tunit)=0;


  // ---- convenience functions ----
  // these functions are implemented in TypeFactory directly, in
  // terms of the interface above, so they're not virtual

  // given an AtomicType, wrap it in a CVAtomicType
  // with no const or volatile qualifiers
  CVAtomicType *makeType(AtomicType *atomic)
    { return makeCVAtomicType(atomic, CV_NONE); }

  // make a ptr-to-'type' type; returns generic Type instead of
  // PointerType because sometimes I return ST_ERROR
  inline Type *makePtrType(Type *type)
    { return type->isError()? type : makePointerType(CV_NONE, type); }

  // map a simple type into its CVAtomicType representative
  CVAtomicType *getSimpleType(SimpleTypeId st, CVFlags cv = CV_NONE);

  // given an array type with no size, return one that is
  // the same except its size is as specified
  ArrayType *setArraySize(SourceLoc loc, ArrayType *type, int size);
};


// This is an implementation of the above interface which returns the
// actual Type-derived objects defined, as opposed to objects of
// further-derived classes.  On the extension topics mentioned above:
//   - It does not deallocate Types at all (oh well...).
//   - It does not (yet) implement hash-consing, except for CVAtomics
//     of SimpleTypes.
//   - No annotations are added; the objects returned have exactly
//     the types declared below.
class BasicTypeFactory : public TypeFactory {
private:   // data
  // global array of non-const, non-volatile built-ins; it's expected
  // to be treated as read-only
  static CVAtomicType unqualifiedSimple[NUM_SIMPLE_TYPES];

public:    // funcs
  // TypeFactory funcs
  virtual CVAtomicType *makeCVAtomicType(AtomicType *atomic, CVFlags cv);
  virtual PointerType *makePointerType(CVFlags cv, Type *atType);
  virtual Type *makeReferenceType(Type *atType);
  virtual FunctionType *makeFunctionType(Type *retType);
  virtual void doneParams(FunctionType *ft);

  virtual ArrayType *makeArrayType(Type *eltType, int size);
  virtual PointerToMemberType *makePointerToMemberType
    (NamedAtomicType *inClassNAT, CVFlags cv, Type *atType);

  virtual Variable *makeVariable(SourceLoc L, StringRef n,
                                 Type *t, DeclFlags f, TranslationUnit *tunit);
};


// this one should be sound; gradually making it more available
template <class T>
inline SObjList<T> const & objToSObjListC(ObjList<T> const &list)
{
  return reinterpret_cast<SObjList<T> const &>(list);
}


// -------------------- XReprSize ---------------------
// thrown when the reprSize() function cannot determine an
// array size
class XReprSize : public xBase {
public:          
  // This is set to true when the reason for failing to determine a
  // size is that a dynamically-sized array was involved (this is a
  // gnu extension).
  //
  // TODO: The better solution is to store the size expression with
  // the array, so I can compute a symbolic expression that evaluates
  // to the array's size.  But that involves changing a lot of stuff.
  bool isDynamic;

public:
  XReprSize(bool isDynamic = false);
  XReprSize(XReprSize const &obj);
  ~XReprSize();
};

void throw_XReprSize(bool isDynamic = false) NORETURN;


// ------ for debugging ------
// The idea here is you say "print type_toString(x)" in gdb, where 'x'
// is a pointer to some type.  The pointer that is returned will be
// printed as a string by gdb.
//
// update: it turns out the latest gdbs are capable of using the
// toString method directly!  but I'll leave this here anyway.
char *type_toString(Type const *t);


// I should explain my intended relationship between references and
// lvalues.  The C++ standard uses the term 'reference' to refer to
// types (a compile-time concept), and 'lvalue' to refer to
// expressions and values (a run-time concept).  Of course, a
// reference type gives rise to an lvalue, and a (non-const) reference
// must be bound to an lvalue, so there's a close relationship between
// the two.  In constrast, the same document uses the term 'pointer'
// when referring to both types and values.
//
// In the interest of reducing the number of distinct concepts, I use
// "reference types" and "lvalues" interchangeably; non-references
// refer to rvalues.  Generally, this works well.  However, one must
// keep in mind that there is consequently a slight terminological
// difference between my stuff and the C++ standard.  For example, in
// the code
//
//   int a;
//   f(a);
//
// the argument 'a' has type 'int' and is an lvalue according to the
// standard, whereas cc_tcheck.cc just says it's an 'int &'.


#endif // CC_TYPE_H
