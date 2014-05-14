// builtinops.h
// data structures to represent cppstd 13.6

#ifndef BUILTINOPS_H
#define BUILTINOPS_H

#include "cc_flags.h"      // BinaryOp
#include "okhashtbl.h"     // OwnerKHashTable

class Type;                // cc_type.h
class Variable;            // variable.h
class Env;                 // cc_env.h
class OverloadResolver;    // overload.h
class ArgumentInfo;        // overload.h


// a set of candidates, usually one line of 13.6; since many of the
// sets in 13.6 are infinite, and the finite ones are large, the
// purpose of this class is to represent those sets in a way that
// allows overload resolution to act *as if* it used the full sets
class CandidateSet {
public:      // funcs
  virtual ~CandidateSet();

  // instantiate the pattern as many times as necessary, given the
  // argument types 'lhsType' and 'rhsType'
  virtual void instantiateBinary(Env &env, OverloadResolver &resolver,
    OverloadableOp op, ArgumentInfo &lhsInfo, ArgumentInfo &rhsInfo)=0;
};
   

// describes a set using polymorphism
class PolymorphicCandidateSet : public CandidateSet {
public:      // data
  // the candidate is represented by a single polymorphic function
  Variable *poly;          // (serf)

public:      // funcs
  PolymorphicCandidateSet(Variable *v);

  virtual void instantiateBinary(Env &env, OverloadResolver &resolver,
    OverloadableOp op, ArgumentInfo &lhsInfo, ArgumentInfo &rhsInfo);
};


// describes a set with predicates over a pairwise analysis
class PredicateCandidateSet : public CandidateSet {
private:     // types
  // a single instantiated candidate; this structure allows us to
  // re-use instantiations
  class Inst {
  public:      // data
    Type *type;       // the type with which the pattern was instantiated
    Variable *inst;   // the instantiation itself

    // clever hack: to ensure that each instantiated candidate is only
    // given to the overload resolution procedure once, I keep track
    // of how many times a given candidate set has requested
    // instantiation, and update the instances with the latest time
    // they were instantiated
    unsigned generation;

  public:      // funcs
    Inst(Type *t, Variable *i)
      : type(t),
        inst(i),
        generation(0)
    {}

    // hashtable accessor functions
    static Type const *getKeyFn(Inst *ic);
    static unsigned hashFn(Type const *t);
    static bool equalFn(Type const *t1, Type const *t2);
  };

public:      // types
  // each potential argument type is passed through this filter before
  // being evaluated as part of a pair; it can return a different
  // type, and it can also return NULL to indicate that the type
  // shouldn't be considered; 'isLeft' says whether this is the left
  // arg or right arg type (actually, none of the filters use this
  // information anymore, but I leave it because it makes sense for
  // the filter to know this)
  typedef Type* (*PreFilter)(Type *t, bool isLeft);

  // after computing a pairwise LUB, the LUB type is passed
  // through this filter; if it returns false, then the type
  // is not used to instantiate the pattern
  typedef bool (*PostFilter)(Type *t);

protected:   // data
  // instantiations that already exist, so we can re-use them
  OwnerKHashTable<Inst, Type> instantiations;

  // instantiation of the ambiguous candidate
  Variable *ambigInst;

  // return type algorithm
  SimpleTypeId retAlgorithm;

  // then this pair of functions filters the argument types to a
  // binary operator in a pairwise analysis to instantiate a pattern
  PreFilter pre;
  PostFilter post;

  // count of the number of times instantiation has happened
  unsigned generation;

protected:   // funcs
  void instantiateCandidate(Env &env,
    OverloadResolver &resolver, OverloadableOp op, Type *T);
  void addAmbigCandidate(Env &env, OverloadResolver &resolver,
    OverloadableOp op);

  virtual Variable *makeNewCandidate(Env &env, OverloadableOp op, Type *T);

public:      // funcs
  PredicateCandidateSet(SimpleTypeId retId, PreFilter pre, PostFilter post);
  ~PredicateCandidateSet();

  virtual void instantiateBinary(Env &env, OverloadResolver &resolver,
    OverloadableOp op, ArgumentInfo &lhsInfo, ArgumentInfo &rhsInfo);
};


// a variant of the predicate set for assignment operators
class AssignmentCandidateSet : public PredicateCandidateSet {
protected:   // funcs
  virtual Variable *makeNewCandidate(Env &env, OverloadableOp op, Type *T);

public:      // funcs
  AssignmentCandidateSet(SimpleTypeId retId, PreFilter pre, PostFilter post);

  virtual void instantiateBinary(Env &env, OverloadResolver &resolver,
    OverloadableOp op, ArgumentInfo &lhsInfo, ArgumentInfo &rhsInfo);
};


// predicate set for the ->* operator
class ArrowStarCandidateSet : public CandidateSet {
private:    // types
  // pair of types, with hashing and equality
  class TypePair {
  public:
    Type *lhsType, *rhsType;    // types for instantiation
    
  public:
    TypePair(Type *L, Type *R)
      : lhsType(L),
        rhsType(R)
    {}
    TypePair(TypePair const &obj)
      : DMEMB(lhsType),
        DMEMB(rhsType)
    {}
    
    string asString() const;
    unsigned hashValue() const;
  };

  // similar to above, for caching candidates
  class Inst {
  public:      // data
    TypePair types;     // types with which the pattern was instantiated
    Variable *inst;     // the instantiation itself

    unsigned generation;

  public:      // funcs
    Inst(TypePair const &t, Variable *i)
      : types(t),
        inst(i),
        generation(0)
    {}

    // hashtable accessor functions
    static TypePair const *getKeyFn(Inst *ic);
    static unsigned hashFn(TypePair const *p);
    static bool equalFn(TypePair const *p1, TypePair const *p2);
  };

private:    // data
  OwnerKHashTable<Inst, TypePair> instantiations;
  
  unsigned generation;

private:    // funcs
  void instantiateCandidate(Env &env,
    OverloadResolver &resolver, Type *lhsType, Type *rhsType);

public:     // funcs
  ArrowStarCandidateSet();
  ~ArrowStarCandidateSet();

  virtual void instantiateBinary(Env &env, OverloadResolver &resolver,
    OverloadableOp op, ArgumentInfo &lhsInfo, ArgumentInfo &rhsInfo);
};


// some pre filters
Type *rvalFilter(Type *t, bool);
Type *rvalIsPointer(Type *t, bool);
Type *para19_20filter(Type *t, bool);
Type *para19_20_andArith_filter(Type *t, bool);

// some post filters
bool pointerToObject(Type *t);
bool pointerOrEnum(Type *t);
bool pointerOrEnumOrPTM(Type *t);
bool pointerOrPTM(Type *t);
bool pointerToAny(Type *t);
bool anyType(Type *t);


#endif // BUILTINOPS_H
