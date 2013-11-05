// variable.h                       see license.txt for copyright and terms of use
// information about a name
// see Diagram 1 of doc/cpp_er.html
//
// Every binding introduction (e.g. declaration) of a name will own
// one of these to describe the introduced name; every reference to
// that name will be annotated with a pointer to the Variable hanging
// off the introduction.   
//
// The name 'variable' is a slight misnomer; it's used for naming:
//   - local and global variables
//   - logic variables (in the verifier)
//   - functions
//   - function parameters
//   - structure fields
//   - enumeration values
//   - typedefs
//   - namespaces
// All of these things can appear in syntactically similar contexts,
// and the lookup rules generally treat them as all being in the
// same lookup space (as opposed to enum and class tag names).
//
// I've decided that, rather than AST nodes trying to own Variables,
// Variables will live in a separate pool (like types) so the AST
// nodes can share them at will.
//
// In fact, my current idea is that the cc_type and variable modules
// are so intertwined they might as well be one.  They share
// dependencies extensively, including the TypeFactory.  So while
// they are (and will remain) physically separate files, they
// should be treated as their own subsystem.

#ifndef VARIABLE_H
#define VARIABLE_H

#include "srcloc.h"            // SourceLoc
#include "strtable.h"          // StringRef
#include "cc_flags.h"          // DeclFlags, ScopeKind
#include "sobjlist.h"          // SObjList
#include "serialno.h"          // INHERIT_SERIAL_BASE

class Type;                    // cc_type.h
class CompoundType;            // cc_type.h
class TypeVisitor;             // cc_type.h
class FunctionType;            // cc_type.h
class OverloadSet;             // below
class Scope;                   // cc_scope.h
class Expression;              // cc.ast
class Function;                // cc.ast
class BasicTypeFactory;        // cc_type.h
class TemplateInfo;            // cc_type.h
class ReadXML;                 // xml.h

string toXml(DeclFlags id);
void fromXml(DeclFlags &out, rostring str);

// FIX: this is temporary; I just want to get the int out and back in
// again for now.
string toXml_Variable_intData(unsigned id);
void fromXml_Variable_intData(unsigned &out, rostring str);

class Variable INHERIT_SERIAL_BASE {
public:    // data
  // for now, there's only one location, and it's the definition
  // location if that exists, else the declaration location; there
  // are significant advantages to storing *two* locations (first
  // declaration, and definition), but I haven't done that yet
  SourceLoc loc;          // location of the name in the source text
                          
  // name introduced (possibly NULL for abstract declarators)
  StringRef name;        

  // type of the variable (NULL iff flags has DF_NAMESPACE)
  Type *type;             

  // whether the variable is a builtin instance member with the
  // default behavior for a default ctor, copy ctor, dtor or assign op.
  bool isBuiltin;

  // whether the variable is a builtin copy constructor.
  // implies isBuiltin.
  bool isBuiltinCopy;

  // various flags; 'const' to force modifications to go through
  // the 'setFlagsTo' method
  const DeclFlags flags;

  // associated value for constant literals, e.g. "const int five = 5;",
  // or default value for function parameters
  //
  // if this Variable is a parameter of a template function, then this
  // 'value' might not have been tchecked; you have to look at the
  // associated TemplateInfo::uninstantiatedDefaultArgs to find out
  Expression *value;      // (nullable serf)

  // default value for template parameters; see TODO at end
  // of this file
  Type *defaultParamType; // (nullable serf)

  // associated function definition; if NULL, either this thing isn't
  // a function or we never saw a definition
  Function *funcDefn;     // (nullable serf)

  // if this name has been overloaded, then this will be a pointer
  // to the set of overloaded names; otherwise it's NULL
  OverloadSet *overload;  // (nullable serf)

  // named scope in which the variable appears; this is only non-NULL
  // if the scope has a name, i.e. it continues to be available for
  // use even after it's lexically closed
  //
  // if this Variable isNamespace(), then 'scope' points at the
  // namespace it names, rather than the containing scope; see
  // getDenotedScope()
  Scope *scope;           // (nullable serf)

private:      // data

  // so serialization/deserialization is possible
  friend class TypeToXml;
  friend class TypeXmlReader;

  // The next two fields are used to store conceptually different
  // things in a single word in order to save space.  I am concerned
  // about the space used by Variable because they are ubiquitous.  I
  // would like to move to a model where Variable is a superclass and
  // there are subclasses for various roles, as that would minimize
  // wasted storage, but that is a fairly big change, and for the
  // moment these localized hacks will suffice.

  // bits 0-7: result of 'getAccess()'
  // bits 8-15: result of 'getScopeKind()'
  // bits 16-31: result of 'getParameterOrdinal()' or 'getBitfieldSize()'
  unsigned intData;

  // for most kinds of Variables, this is 'getUsingAlias()'; for
  // template parameters (isTemplateParam()), this is
  // 'getParameterizedEntity()'
  Variable *usingAlias_or_parameterizedEntity;   // (nullable serf)

  // for templates, this is the list of template parameters and other
  // template stuff; for a primary it includes a list of
  // already-instantiated versions
  //
  // this is private to force clients to go through templateInfo(),
  // which skips aliases, as aliases now share templateInfos with
  // the things they are aliases of
  TemplateInfo *templInfo;      // (owner)

protected:    // funcs
  friend class BasicTypeFactory;
  Variable(SourceLoc L, StringRef n, Type *t, DeclFlags f);
  Variable(ReadXML&);           // ctor for de-serialization

public:
  virtual ~Variable();

  bool hasFlag(DeclFlags f) const { return (flags & f) != 0; }
  bool hasAnyFlags(DeclFlags /*union*/ f) const { return (flags & f) != 0; }
  bool hasAllFlags(DeclFlags /*union*/ f) const { return (flags & f) == f; }

  void setFlag(DeclFlags f) { setFlagsTo(flags | f); }
  void addFlags(DeclFlags f) { setFlag(f); }
  void clearFlag(DeclFlags f) { setFlagsTo(flags & ~f); }

  // change the value of 'flags'; this is virtual so that annotation
  // systems can monitor flag modifications
  virtual void setFlagsTo(DeclFlags f);

  // some convenient interpretations of 'flags'
  bool hasAddrTaken() const { return hasFlag(DF_ADDRTAKEN); }
  bool isGlobal() const { return hasFlag(DF_GLOBAL); }
  bool isStatic() const { return hasFlag(DF_STATIC); }
  bool isMember() const { return hasFlag(DF_MEMBER); }
  bool isNamespace() const { return hasFlag(DF_NAMESPACE); }
  bool isImplicitTypedef() const { return hasAllFlags(DF_IMPLICIT | DF_TYPEDEF); }
  bool isImplicitMemberFunc() const { return hasFlag(DF_IMPLICIT) && !hasFlag(DF_TYPEDEF); }
  bool isEnumerator() const { return hasFlag(DF_ENUMERATOR); }
  bool isType() const { return hasFlag(DF_TYPEDEF); }

  // true if this name refers to a class or struct or union
  bool isClass() const;

  // refers to a user-provided typedef
  bool isExplicitTypedef() const 
    { return hasFlag(DF_TYPEDEF) && !hasFlag(DF_IMPLICIT); }

  // access control applied to this variable in the context
  // in which it appears (defaults to AK_PUBLIC)
  AccessKeyword getAccess() const;
  void setAccess(AccessKeyword k);

  // kind of scope in which the name is declared; initially this
  // is SK_UNKNOWN
  //
  // 2005-03-02: It appears that this quantity is never actually used;
  // furthermore, I think it is computable (mainly from 'scope').  So,
  // it is a candidate for removal at some point.
  ScopeKind getScopeKind() const;
  void setScopeKind(ScopeKind k);

  // for template parameters, this says which parameter this is in
  // the parameter list, e.g., 0 for first, 1 for second, etc.
  int getParameterOrdinal() const;
  void setParameterOrdinal(int ord);

  // true if this name refers to a template function, or is
  // the typedef-name of a template class (or partial specialization)
  //
  // if 'considerInherited' is false, then the template-ness
  // is only as w.r.t. its containing class
  bool isTemplate(bool considerInherited = true) const;
  bool isTemplateFunction(bool considerInherited = true) const;
  bool isTemplateClass(bool considerInherited = true) const;

  // true if this is an instantiation of a template
  bool isInstantiation() const;

  // templates (and specializations) and instantiatons have
  // TemplateInfo
  TemplateInfo *templateInfo() const;
  void setTemplateInfo(TemplateInfo *templInfo0);

  // Are there templatized variables (such as type variables) that are
  // not in the template info template parameters?
  bool notQuantifiedOut();

  // are we an uninstantiated template or a member of one?
  bool isUninstTemplateMember() const;

  // variable's type.. same as the public 'type' field..
  Type *getType() { return type; }
  Type const *getTypeC() const { return type; }

  // create an overload set if it doesn't exist, and return it (do not
  // do this unless you actually need a set; if you just want to treat
  // overloaded and non-overloaded variables uniformly, use
  // 'getOverloadList' instead)
  OverloadSet *getOrCreateOverloadSet();

  // return the set of overloaded entities; this might just
  // be the singleton 'this', if it isn't overloaded
  void getOverloadList(SObjList<Variable> &set);

  // true if this name is overloaded
  bool isOverloaded() const { return !!overload; }

  // number of elements in the overload set, or 1 if there is no
  // overload set
  int overloadSetSize() const;

  // true if this is a member of a template (uninstantiated template)
  bool isMemberOfTemplate() const;

  // true if this is a template parameter or bound arg or both
  bool isAbstractTemplateParam() const 
    { return hasFlag(DF_TEMPL_PARAM) && !hasFlag(DF_BOUND_TPARAM); }
  bool isBoundTemplateParam() const
    { return hasAllFlags(DF_TEMPL_PARAM | DF_BOUND_TPARAM); }
  bool isTemplateParam() const
    { return hasFlag(DF_TEMPL_PARAM); }
    
  // true if this is a template type parameter (unbound/abstract)
  bool isTemplateTypeParam() const;

  // generic print (C or ML depending on Type::printAsML)
  string toString() const;

  // C declaration syntax
  string toCString() const;

  // syntax when used in a parameter list
  string toCStringAsParameter() const;

  // ML-style
  string toMLString() const;

  // toString+newline to cout
  void gdb() const;

  // fully qualified but not mangled name
  string fullyQualifiedName() const;

  // like toString but with the fully qualified name
  string toQualifiedString() const;

  // hook for verifier: text to be printed after the variable's name
  // in declarator syntax
  virtual string namePrintSuffix() const;    // default: ""

  // if this is variable is actually an alias for another one, via a
  // "using declaration" (cppstd 7.3.3), then this points to the one
  // it is an alias of; otherwise NULL; see comments near
  // implementation of skipAliasC
  Variable *getUsingAlias() const;
  void setUsingAlias(Variable *target);

  // if this variable is a template parameter, then this says which
  // template entity is paramterized by it; otherwise NULL
  Variable *getParameterizedEntity() const;
  void setParameterizedEntity(Variable *templ);
                                                          
  // true if 'this' and 'other' are the same ordinal parameter of
  // the same template entity
  bool sameTemplateParameter(Variable const *other) const;

  // follow the 'usingAlias' field if non-NULL; otherwise return this
  Variable const *skipAliasC() const;
  Variable *skipAlias() { return const_cast<Variable*>(skipAliasC()); }

  // true if this name refers to a template (function) or an overload
  // set that includes one
  bool namesTemplateFunction() const;
  
  // this must be an enumerator; get the integer value it denotes
  int getEnumeratorValue() const;

  // bitfield access
  bool isBitfield() const { return hasFlag(DF_BITFIELD); }
  void setBitfieldSize(int bits);      // must be bitfield
  int getBitfieldSize() const;         // must be bitfield

  // this variable refers to a scope; get it
  Scope *getDenotedScope() const;

  // dsw: Variables are part of the type system at least for purposes
  // of traversal
  void traverse(TypeVisitor &vis);
};

inline string toString(Variable const *v) { return v->toString(); }

// true if 'v1' and 'v2' refer to the same run-time entity
bool sameEntity(Variable const *v1, Variable const *v2);


class OverloadSet {
public:
  // list-as-set
  SObjList<Variable> set;
  
public:
  OverloadSet();
  ~OverloadSet();
  
  void addMember(Variable *v);
  int count() const { return set.count(); }

  // These are obsolete; see Env::findInOverloadSet.              
  //
  // Update: But Oink wants to use them for linker imitation.. and
  // I don't see much harm in that, since non-concrete types should
  // not be linker visible anyway.
  Variable *findByType(FunctionType const *ft, CVFlags receiverCV);
  Variable *findByType(FunctionType const *ft);
};


// This function renders an Expression as a string, if it knows how
// to.  This function is here to cut the dependency between Types and
// the AST.  If the AST-aware modules are compiled into this program,
// then this function just calls into them, prepending the prefix; but
// if not, then this always returns "".
string renderExpressionAsString(char const *prefix, Expression const *e);


/*
TODO: More efficient storage for Variable.

First, I want to make a class hierarchy like this:

  - Variable
    - TypeVariable: things that currently have DF_TYPEDEF
      - TypeParamVariable: template type paramters; make up
        a new DeclFlag to distinguish them (DF_TEMPL_PARAM?)
        [has defaultTypeArg]
      - ClassVariable: DF_TYPEDEF where 'type->isClassType()'
        [has templInfo]
    - ObjectVariable: no DF_TYPEDEF
      [has value]
      - FunctionVariable: objects where 'type->isFunctionType()'
        [has templInfo]
        [has funcDefn]
        [has overload]
      - Enumerator (obviates EnumType::Value)
    - AliasVariable (DF_USING_ALIAS?)
      [has usingAlias]
    - NamespaceVariable (?? how to namespaces name their space?)

Second, I want to collapse 'access' and 'scopeKind', since
these fields waste most of their bits.  Perhaps when DeclFlags
gets split I can arrange a storage sharing strategy among the
(then four) fields that are bit-sets.

*/

#endif // VARIABLE_H
