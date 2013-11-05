// mflags.h
// MatchFlags enumeration, so I can #include just that without
// getting all of mtype.h

#ifndef MFLAGS_H
#define MFLAGS_H

#include "macros.h"      // ENUM_BITWISE_OPS
#include "str.h"         // string

enum MatchFlags {
  // complete equality; this is the default; note that we are
  // checking for *type* equality, rather than equality of the
  // syntax used to denote it, so we do *not* compare (e.g.)
  // function parameter names or typedef usage
  MF_NONE            = 0x0000,

  // ----- basic behaviors -----
  // when comparing function types, do not check whether the
  // return types are equal
  MF_IGNORE_RETURN   = 0x0001,

  // when comparing function types, if one is a nonstatic member
  // function and the other is not, then do not (necessarily)
  // call them unequal
  MF_STAT_EQ_NONSTAT = 0x0002,    // static can equal nonstatic

  // when comparing function types, only compare the explicit
  // (non-receiver) parameters; this does *not* imply
  // MF_STAT_EQ_NONSTAT
  MF_IGNORE_IMPLICIT = 0x0004,

  // In the C++ type system, cv qualifiers on parameters are not part
  // of the type [8.3.5p3], so by default mtype ignores them.  If you
  // set this flag, then they will *not* be ignored.  It is provided
  // only for completeness; Elsa does not use it.
  MF_RESPECT_PARAM_CV= 0x0008,

  // ignore the topmost cv qualification of the two types compared
  MF_IGNORE_TOP_CV   = 0x0010,

  // when comparing function types, compare the exception specs;
  // by default such specifications are not compared because the
  // exception spec is not part of the "type" [8.3.5p4]
  MF_COMPARE_EXN_SPEC= 0x0020,
  
  // allow the cv qualifications to differ up to the first type
  // constructor that is not a pointer or pointer-to-member; this
  // is cppstd 4.4 para 4 "similar"; implies MF_IGNORE_TOP_CV
  MF_SIMILAR         = 0x0040,

  // when the second type in the comparison is polymorphic (for
  // built-in operators; this is not for templates), and the first
  // type is in the set of types described, say they're equal;
  // note that polymorhism-enabled comparisons therefore are not
  // symmetric in their arguments
  MF_POLYMORPHIC     = 0x0080,

  // for use by the matchtype module: this flag means we are trying
  // to deduce function template arguments, so the variations
  // allowed in 14.8.2.1 are in effect (for the moment I don't know
  // what propagation properties this flag should have)
  MF_DEDUCTION       = 0x0100,

  // this is another flag for MatchTypes, and it means that template
  // parameters should be regarded as unification variables only if
  // they are *not* associated with a specific template
  MF_UNASSOC_TPARAMS = 0x0200,

  // ignore the cv qualification on the array element, if the
  // types being compared are arrays
  MF_IGNORE_ELT_CV   = 0x0400,

  // enable matching/substitution with template parameters
  MF_MATCH           = 0x0800,

  // do not allow new bindings to be created; but existing bindings
  // can continue to be used
  MF_NO_NEW_BINDINGS = 0x1000,

  // when combined with MF_MATCH, it means we can bind variables in
  // the pattern only to other variables in the "concrete" type, and
  // that the binding function must be injective (no two pattern
  // variables can be bound to the same concrete variable); this
  // is used to compare two templatized signatures for equivalence
  MF_ISOMORPHIC      = 0x2000,

  // ----- combined behaviors -----
  // all flags set to 1
  MF_ALL             = 0x3FFF,

  // number of 1 bits in MF_ALL
  MF_NUM_FLAGS       = 14,

  // signature equivalence for the purpose of detecting whether
  // two declarations refer to the same entity (as opposed to two
  // overloaded entities)
  MF_SIGNATURE       = (
    MF_IGNORE_RETURN |       // can't overload on return type
    MF_STAT_EQ_NONSTAT       // can't overload on static vs. nonstatic
  ),

  // ----- combinations used by the mtype implementation -----
  // this is the set of flags that allow CV variance within the
  // current type constructor
  MF_OK_DIFFERENT_CV = (MF_IGNORE_TOP_CV | MF_SIMILAR),

  // this is the set of flags that automatically propagate down
  // the type tree equality checker; others are suppressed once
  // the first type constructor looks at them
  MF_PROP = (
    MF_RESPECT_PARAM_CV |
    MF_POLYMORPHIC      |
    MF_UNASSOC_TPARAMS  |
    MF_MATCH            |
    MF_NO_NEW_BINDINGS  |
    MF_ISOMORPHIC       
    
    // Note: MF_COMPARE_EXN_SPEC is *not* propagated.  It is used only
    // when the compared types are FunctionTypes, to compare those
    // toplevel exn specs, but any FunctionTypes appearing underneath
    // are compared just as types (not objects), and hence their exn
    // specs are irrelevant.
  ),

  // these flags are propagated below ptr and ptr-to-member
  MF_PTR_PROP = (
    MF_PROP            |
    MF_SIMILAR         |
    MF_DEDUCTION
  )
};

ENUM_BITWISE_OPS(MatchFlags, MF_ALL)

// defined in mtype.cc
string toString(MatchFlags flags);


#endif // MFLAGS_H
