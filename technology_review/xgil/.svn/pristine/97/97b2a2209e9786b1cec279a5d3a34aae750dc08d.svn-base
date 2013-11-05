// mtype.h
// new implementation of type matcher

// 2005-07-24: The plan for this module is it will eventually replace
// the 'matchtype' module, and also Type::equals.  However, right now
// it is still being put through its paces and so just exists on the
// side as an auxiliary module, only reachable via the __test_mtype
// internal testing hook function, exercised for the moment only by
// in/t0511.cc.

#ifndef MTYPE_H
#define MTYPE_H

#include "mflags.h"             // MatchFlags
#include "objmap.h"             // ObjMap
#include "cc_type.h"            // Type
#include "cc_ast.h"             // C++ AST
#include "template.h"           // STemplateArgument

class Env;                      // cc_env.h

class MType;                    // this file


// Internal MType: the core of the MType implementation, separated
// into its own class so that it cannot (easily, accidentally) use the
// public MType interfaces.  Its directly-exposed interfaces ensure
// constness of arguments, except that the exposed 'bindings' map can
// be used for non-const access.  The MType class is responsible for
// packaging this in a sound form.
class IMType {
protected:   // types
  // A template variable binding.  A name can be bound to one of three
  // things:
  //   - a Type object and CVFlags to modify it
  //   - an AtomicType object (with no cv)
  //   - a non-type value given by 'sarg'
  // The first two options are similar, differing only because it avoids
  // having to wrap a Type object around an AtomicType object.
  //
  // Public clients don't have to know about this trickery though; as
  // far as they are concerned, a name is simply bound to an
  // STemplateArgument (though they have to pass a TypeFactory to
  // allow the internal representation to be converted).
  class Binding {
  public:    // data
    STemplateArgument sarg;     // most of the binding info
    CVFlags cv;                 // if sarg.isType(), we are bound to the 'cv' version of it

  public:
    Binding() : sarg(), cv(CV_NONE) {}
    Binding(Binding const &obj) : sarg(obj.sarg), cv(obj.cv) {}

    bool operator== (Binding const &obj) const;

    // Though I am using 'STemplateArgument', I want to treat its
    // 'Type*' as being const.
    void setType(Type const *t) { sarg.setType(const_cast<Type*>(t)); }
    Type const *getType() const { return sarg.getType(); }
                            
    // debugging
    string asString() const;
  };

protected:   // data
  // set of bindings
  typedef ObjMap<char const /*StringRef*/, Binding> BindingMap;
  BindingMap bindings;
  
  // This is used to resolve DQTs during matching.  Originally I'd
  // hoped to keep MType unaware of the environment, but this now
  // seems unavoidable.  On the bright side, it means I can remove
  // all PQName resolution code from MType, since Env can do that.
  Env *env;                    // (nullable serf)

public:      // data                    
  // This is set to true if a failure to resolve a DQT is the cause of
  // a match failure.  It starts as false, but once set to true, MType
  // does not reset it, so it is up to the caller to reset this flag
  // between queries when appropriate.
  bool failedDueToDQT;

protected:   // funcs
  // ******************************************************************
  // * NOTE: Do *not* simply make these entry points public.  If you  *
  // * need to call one of these, make a public wrapper that consults *
  // * 'allowNonConst' and uses TRACE("mtype") appropriately.         *
  // ******************************************************************
  static bool canUseAsVariable(Variable *var, MatchFlags flags);
  bool imatchAtomicType(AtomicType const *conc, AtomicType const *pat, MatchFlags flags);
  bool imatchTypeVariable(TypeVariable const *conc, TypeVariable const *pat, MatchFlags flags);
  bool imatchPseudoInstantiation(PseudoInstantiation const *conc,
                                       PseudoInstantiation const *pat, MatchFlags flags);
  bool imatchSTemplateArguments(ObjList<STemplateArgument> const &conc,
                               ObjList<STemplateArgument> const &pat,
                               MatchFlags flags);
  bool imatchSTemplateArgument(STemplateArgument const *conc,
                                     STemplateArgument const *pat, MatchFlags flags);
  bool imatchNontypeWithVariable(STemplateArgument const *conc,
                                       E_variable *pat, MatchFlags flags);
  bool addBinding(StringRef name, Binding * /*owner*/ value, MatchFlags flags);
  bool imatchDependentQType(DependentQType const *conc,
                                  DependentQType const *pat, MatchFlags flags);
  bool imatchPQName(PQName const *conc, PQName const *pat, MatchFlags flags);
  bool imatchType(Type const *conc, Type const *pat, MatchFlags flags);
  bool imatchTypeWithVariable(Type const *conc, TypeVariable const *pat,
                                    CVFlags tvCV, MatchFlags flags);
  bool imatchTypeWithResolvedType(Type const *conc, Type const *pat,
                                  MatchFlags flags);
  bool imatchTypeWithDQT(Type const *conc, DependentQType const *pat,
                         CVFlags patCV, MatchFlags flags);
  bool equalWithAppliedCV(Type const *conc, Binding *binding, CVFlags cv, MatchFlags flags);
  bool imatchTypeWithSpecifiedCV(Type const *conc, Type const *pat, CVFlags cv, MatchFlags flags);
  bool addTypeBindingWithoutCV(StringRef tvName, Type const *conc,
                               CVFlags tvcv, MatchFlags flags);
  bool imatchTypeWithPolymorphic(Type const *conc, SimpleTypeId polyId, MatchFlags flags);
  bool imatchAtomicTypeWithVariable(AtomicType const *conc,
                                   TypeVariable const *pat,
                                   MatchFlags flags);
  bool imatchCVAtomicType(CVAtomicType const *conc, CVAtomicType const *pat, MatchFlags flags);
  bool imatchCVFlags(CVFlags conc, CVFlags pat, MatchFlags flags);
  bool imatchPointerType(PointerType const *conc, PointerType const *pat, MatchFlags flags);
  bool imatchReferenceType(ReferenceType const *conc, ReferenceType const *pat, MatchFlags flags);
  bool imatchFunctionType(FunctionType const *conc, FunctionType const *pat, MatchFlags flags);
  bool imatchParameterLists(FunctionType const *conc, FunctionType const *pat,
                                  MatchFlags flags);
  bool imatchExceptionSpecs(FunctionType const *conc, FunctionType const *pat, MatchFlags flags);
  bool imatchArrayType(ArrayType const *conc, ArrayType const *pat, MatchFlags flags);
  bool imatchPointerToMemberType(PointerToMemberType const *conc,
                                       PointerToMemberType const *pat, MatchFlags flags);
  bool imatchExpression(Expression const *conc, Expression const *pat, MatchFlags flags);

private:     // funcs
  // the only allowed subclass is MType; this justifies a
  // static_cast in mtype.cc
  friend class MType;
  IMType();
  ~IMType();
};


// the public interface
class MType : protected IMType {
private:     // funcs
  // This flag is true if the client is using the non-const interface.
  //
  // The idea is this module can support one of two modes
  // w.r.t. constness:
  //   1) The module promises not to modify any of its arguments.  The
  //      client can use 'match', but cannot retrieve bindings (because
  //      the bindings expose non-const access).
  //      -> A possible future extension is to provide a binding query
  //         interface that only exposes const access, but as that is
  //         not needed right now, it is not provided.
  //   2) The module makes no promises about modification.  The client
  //      must use 'matchNC', and can query bindings freely.
  // The private functions act as if the module is always in 'const' mode,
  // that is, they promise to never modify the arguments; query is the
  // one exception.
  //
  // The rationale for such deliberate treatment of 'const' is that I
  // want to be able to use this module both for Type equality, which
  // ought to be queryable with a const interface, and Type matching,
  // which needs binding queries, which are at best inconvenient to
  // provide with a const interface.
  bool const allowNonConst;

private:     // funcs
  string bindingsToString() const;
  bool commonMatchType(Type const *conc, Type const *pat, MatchFlags flags);
  bool commonMatchSTemplateArguments(ObjList<STemplateArgument> const &conc,
                                     ObjList<STemplateArgument> const &pat,
                                     MatchFlags flags);

public:      // funcs
  // if 'allowNonConst' is false, const match* can be invoked;
  // if 'allowNonConst' is true, 'getBoundValue' be invoked
  MType(bool allowNonConst = false);
  ~MType();

  // This constructor sets 'allowNonConst' to true and also
  // provides the 'env' for resolving DQTs.
  MType(Env &env);

  // so I can supply an Env even in const mode
  //
  // 2005-08-14: Can't allow this.  See imatchWithResolvedType.
  // If you need to resolve DQTs, you have to allowNonConst, so
  // the Env can/must be provided in the constructor call.
  //void setEnv(Env *e) { env=e; }
  
  // what constness mode are we in?
  bool getAllowNonConst() const { return allowNonConst; }

  // Publish this member; see its comments above.
  IMType::failedDueToDQT;

  // ---- const match ----
  // these functions can only be called if 'allowNonConst' is false

  // return true if 'conc' is an instance of 'pat', in which case this
  // object will have a record of the instantiation bindings; the
  // const version can only be called when 'nonConst' is false
  bool matchType(Type const *conc, Type const *pat, MatchFlags flags);
  
  // a few more
  bool matchSTemplateArguments(ObjList<STemplateArgument> const &conc,
                               ObjList<STemplateArgument> const &pat,
                               MatchFlags flags);
  bool matchAtomicType(AtomicType const *conc, AtomicType const *pat,
                       MatchFlags flags);
  bool matchSTemplateArgument(STemplateArgument const *conc,
                              STemplateArgument const *pat, MatchFlags flags);
  bool matchExpression(Expression const *conc, Expression const *pat, MatchFlags flags);

  // ---- non-const match ----
  // for now, only selected non-const entry points are provided
  bool matchTypeNC(Type *conc, Type *pat, MatchFlags flags);
  bool matchSTemplateArgumentsNC(ObjList<STemplateArgument> &conc,
                                 ObjList<STemplateArgument> &pat,
                                 MatchFlags flags);

  // ---- query ----
  // how many bindings are currently active?
  int getNumBindings() const;

  // returns true if 'name' is bound to something; this *can* be
  // called even when 'allowNonConst' is false
  bool isBound(StringRef name) const;

  // get the binding for 'name', or return STA_NONE if none;
  // 'allowNonConst' must be true
  STemplateArgument getBoundValue(StringRef name, TypeFactory &tfac) const;

  // set a binding; 'value' must not be STA_NONE
  void setBoundValue(StringRef name, STemplateArgument const &value);
};


#endif // MTYPE_H
