// lookupset.h
// LookupSet, a set of lookup candidates

#ifndef LOOKUPSET_H
#define LOOKUPSET_H

#include "sobjlist.h"        // SObjList
#include "str.h"             // string

class Variable;              // variable.h


// variable lookup sometimes has complicated exceptions or
// special cases, so I'm folding lookup options into one value
enum LookupFlags {
  LF_NONE              = 0,
  LF_INNER_ONLY        = 0x00000001,   // only look in the innermost scope
  LF_ONLY_TYPES        = 0x00000002,   // ignore (skip over) non-type names
  LF_TYPENAME          = 0x00000004,   // user used 'typename' keyword
  LF_SKIP_CLASSES      = 0x00000008,   // skip class scopes
  LF_ONLY_NAMESPACES   = 0x00000010,   // ignore non-namespace names
  LF_TYPES_NAMESPACES  = 0x00000020,   // ignore non-type, non-namespace names
  LF_QUALIFIED         = 0x00000040,   // context is a qualified lookup
  LF_TEMPL_PRIMARY     = 0x00000080,   // return template primary rather than instantiating it
  LF_FUNCTION_NAME     = 0x00000100,   // looking up the name at a function call site
  LF_DECLARATOR        = 0x00000200,   // context is a declarator name lookup; for templates, this means to pick the primary or a specialization, but don't instantiate
  LF_SELFNAME          = 0x00000400,   // the DF_SELFNAME is visible
  LF_unused_value2     = 0x00000800,   // (available)
  LF_TEMPL_PARAM       = 0x00001000,   // return only template parameter/argument names
  LF_SUPPRESS_ERROR    = 0x00002000,   // during lookup, don't emit errors
  LF_SUPPRESS_NONEXIST = 0x00004000,   // suppress "does not exist" errors
  LF_IGNORE_USING      = 0x00008000,   // 3.4.2p3: ignore using-directives
  LF_NO_IMPL_THIS      = 0x00010000,   // do not insert implicit 'this->'
  LF_unused_value3     = 0x00020000,   // (available)
  LF_QUERY_TAGS        = 0x00040000,   // look in Scope::typeTags instead of Scope::variables
  LF_unused_value      = 0x00080000,   // (available for a new use)
  LF_EXPECTING_TYPE    = 0x00100000,   // do not apply template args to a non-type
  LF_EXPLICIT_INST     = 0x00200000,   // the context is a TF_explicitInst
  LF_ARG_DEP           = 0x00400000,   // looking in argument-dependent "associated scopes"
  LF_GET_SCOPE_ONLY    = 0x00800000,   // if looking up A::B::C, just look up A::B

  // flag combination for looking up names that precede "::" (3.4.3p1);
  // this is used for the new lookup mechanism (Env::lookupPQ, etc.)
  LF_QUALIFIER_LOOKUP  = LF_TYPES_NAMESPACES | LF_SELFNAME,

  LF_ALL_FLAGS         = 0x00FFFFFF,   // bitwise OR of all flags
  NUM_LOOKUPFLAGS      = 24            // # of bits set to 1 in LF_ALL_FLAGS
};

extern char const * const lookupFlagNames[NUM_LOOKUPFLAGS];
string toString(LookupFlags flags);
string toString_LF(LookupFlags flags);

ENUM_BITWISE_OPS(LookupFlags, LF_ALL_FLAGS)     // smbase/macros.h


// filter a Variable w.r.t. a given set of flags, returning NULL
// if the Variable does not pass through the filter  
Variable *vfilter(Variable *v, LookupFlags flags);


// set of lookup candidates; equivalence classes are as identified
// by 'sameEntity' (declared in variable.h)
class LookupSet : public SObjList<Variable> {
private:     // disallowed
  void operator== (LookupSet&);

public:
  LookupSet();
  ~LookupSet();
  
  // copy list contents
  LookupSet(LookupSet const &obj);
  LookupSet& operator= (LookupSet const &obj);
  void copy(LookupSet const &obj);

  // like vfilter, but also accumulate the Variable in the set
  Variable *filter(Variable *v, LookupFlags flags);

  // add 'v' to a candidate set, such that the set has exactly one
  // entry for each unique entity; this breaks apart 'v' if it is
  // an overload set and enters each overloaded entity separately
  void adds(Variable *v);

  // same as above except add 'v' itself, ignoring whether it
  // is an overload set
  void add(Variable *v);
  
  // throw away all the entries except for one; this is used for
  // error recovery
  void removeAllButOne();
  
  // remove any non-templates from the set
  void removeNonTemplates();
  
  // construct a candidate list, one per line, indented
  string asString() const;
  void gdb() const;
};


#endif // LOOKUPSET_H
