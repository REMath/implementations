// stdconv.cc                       see license.txt for copyright and terms of use
// code for stdconv.h

#include "stdconv.h"      // this module
#include "cc_type.h"      // Type
#include "cc_env.h"       // Env
#include "trace.h"        // tracingSys


/*
 * 2005-04-03: ARR_QUAL_CONV:
 *
 * It is possible to convert (say)
 *
 *   pointer to array of int
 *
 * to
 *
 *   pointer to array of const int
 *
 * because 3.9.3p5 apparently intends cv qualifiers on arrays and
 * array elements to be interchangeable with respect to standard
 * conversions.  See this post:
 *
 *   http://groups-beta.google.com/group/comp.std.c++/msg/1396c9ff05f4e86f?dmode=source
 *
 * So the strategy in this module (marked with "ARR_QUAL_CONV")
 * is to "pull" qualifiers on array elements up to the level of
 * the (outermost) ArrayType, as if they were attached to that
 * object (only).  This is done primarily by 'getSrcCVFlags'.
 */


// ----------------------- StandardConversion -------------------
string toString(StandardConversion c)
{
  stringBuilder sb;

  if (c == SC_ERROR) {
    return string("SC_ERROR");
  }

  if (c == SC_IDENTITY) {
    return string("SC_IDENTITY");
  }

  #define CASE(label)                  \
    case label:                        \
      if (sb.length()) { sb << "|"; }  \
      sb << #label;                    \
      break;

  switch (c & SC_GROUP_1_MASK) {
    default: return stringc << "bad code: " << (int)c;
    case SC_IDENTITY: break;
    CASE(SC_LVAL_TO_RVAL)
    CASE(SC_ARRAY_TO_PTR)
    CASE(SC_FUNC_TO_PTR)
  }

  switch (c & SC_GROUP_3_MASK) {
    default: return stringc << "bad code: " << (int)c;
    case SC_IDENTITY: break;
    CASE(SC_QUAL_CONV)
  }

  switch (c & SC_GROUP_2_MASK) {
    default: return stringc << "bad code: " << (int)c;
    case SC_IDENTITY: break;
    CASE(SC_INT_PROM)
    CASE(SC_FLOAT_PROM)
    CASE(SC_INT_CONV)
    CASE(SC_FLOAT_CONV)
    CASE(SC_FLOAT_INT_CONV)
    CASE(SC_PTR_CONV)
    CASE(SC_PTR_MEMB_CONV)
    CASE(SC_BOOL_CONV)
  }

  #undef CASE

  if (c & ~(SC_GROUP_1_MASK | SC_GROUP_2_MASK | SC_GROUP_3_MASK)) {
    return stringc << "bad code: " << (int)c;
  }

  return sb;
}


StandardConversion removeLval(StandardConversion scs)
{
  if ((scs & SC_GROUP_1_MASK) == SC_LVAL_TO_RVAL) {
    // remove this transformation
    return scs & (SC_GROUP_2_MASK | SC_GROUP_3_MASK);
  }
  else {
    return scs;
  }
}


bool isSubsequenceOf(StandardConversion left, StandardConversion right)
{
  StandardConversion L, R;
  
  L = left & SC_GROUP_1_MASK;                                   
  R = right & SC_GROUP_1_MASK;
  if (!( L == SC_IDENTITY || L == R )) {
    return false;
  }

  L = left & SC_GROUP_2_MASK;
  R = right & SC_GROUP_2_MASK;
  if (!( L == SC_IDENTITY || L == R )) {
    return false;
  }

  L = left & SC_GROUP_3_MASK;
  R = right & SC_GROUP_3_MASK;
  if (!( L == SC_IDENTITY || L == R )) {
    return false;
  }

  return true;
}


// ---------------------------- SCRank ----------------------------
// table 9
SCRank getRank(StandardConversion scs)
{
  if ((scs & SC_GROUP_2_MASK) >= SC_INT_CONV) {
    return SCR_CONVERSION;
  }
  
  if (scs & SC_GROUP_2_MASK) {
    return SCR_PROMOTION;
  }
  
  return SCR_EXACT;
}


// --------------------- getStandardConversion --------------------
bool isIntegerPromotion(AtomicType const *src, AtomicType const *dest);

// int (including bitfield), bool, or enum
bool isIntegerNumeric(Type const *t, SimpleType const *tSimple)
{
  if (tSimple) {
    return isIntegerType(tSimple->type) ||
           tSimple->type == ST_BOOL ||
           tSimple->type == ST_PROMOTED_INTEGRAL;
  }

  // TODO: bitfields are also a valid integer conversion source,
  // once I have an explicit representation for them

  return t->isEnumType();
}

// any of above, or float
bool isNumeric(Type const *t, SimpleType const *tSimple)
{
  return isIntegerNumeric(t, tSimple) ||
         (tSimple && isFloatType(tSimple->type)) ||
         (tSimple && tSimple->type == ST_PROMOTED_ARITHMETIC);
}


#if 0   // unused, but potentially useful at some point
static char const *atomicName(AtomicType::Tag tag)
{
  switch (tag) {
    default: xfailure("bad tag");
    case AtomicType::T_SIMPLE:   return "simple";
    case AtomicType::T_COMPOUND: return "compound";
    case AtomicType::T_ENUM:     return "enum";
    case AtomicType::T_TYPEVAR:  return "type variable";
  }
}
#endif // 0

static char const *ctorName(Type::Tag tag)
{
  switch (tag) {
    default: xfailure("bad tag");
    case Type::T_ATOMIC:          return "atomic";
    case Type::T_POINTER:         return "pointer";
    case Type::T_FUNCTION:        return "function";
    case Type::T_ARRAY:           return "array";
    case Type::T_POINTERTOMEMBER: return "ptr-to-member";
  }
}


// implementation class
class Conversion {
public:
  // original parameters to 'getStandardConversion'
  string *errorMsg;
  SpecialExpr srcSpecial;
  Type const *src;
  Type const *dest;
  bool destIsReceiver;

  // eventual return value
  StandardConversion ret;

  // when true, every destination pointer type constructor
  // has had 'const' in its cv flags
  bool destConst;

  // count how many pointer or ptr-to-member type ctors we
  // have stripped so far
  int ptrCtorsStripped;

public:
  Conversion(string *e, SpecialExpr sp, Type const *s, Type const *d, bool dir)
    : errorMsg(e),
      srcSpecial(sp),
      src(s),
      dest(d),
      destIsReceiver(dir),

      ret(SC_IDENTITY),
      destConst(true),
      ptrCtorsStripped(0)
  {}

  StandardConversion error(char const *why);

  bool stripPtrCtor(CVFlags scv, CVFlags dcv, bool isReference=false);
};


StandardConversion Conversion::error(char const *why)
{
  // 10/02/04: This is probably not the best way to handle this, but one
  // problem with 'getStandardConversion' is if the source and destination
  // are both references, it wants to pair those references up, but it is
  // also possible to implicitly convert away the source reference and bind
  // the dest reference, *if* the dest reference is a reference to const.
  //
  // So, if we are about to report an error (which is why we are in
  // this function), and the dest is 'T const &', try again with a
  // dest of just 'T'.
  if (dest->isReference() &&
      dest->getAtType()->isConst()) {
    return getStandardConversion(errorMsg, srcSpecial, src, dest->getAtType(),
                                 destIsReceiver);
  }

  if (errorMsg) {
    *errorMsg = stringc
      << "cannot convert `" << src->toString()
      << "' to `" << dest->toString()
      << "': " << why;
  }
  return ret = SC_ERROR;
}


// strip pointer constructors, update local state; return true
// if we've encountered an error, in which case 'ret' is set
// to the error code to return
bool Conversion::stripPtrCtor(CVFlags scv, CVFlags dcv, bool isReference)
{
  if (scv != dcv) {
    if (isReference) {
      // Conversion from 'int &' to 'int const &' is equivalent to
      // SC_LVAL_TO_RVAL, or so I'm led to believe by 13.3.3.2 para 3,
      // second example.  13.3.3.1.4 para 5 talks about "reference-
      // compatible with added qualification", but I don't then see
      // a later discussion of what exactly this means.
      //
      // update: that term is defined in 8.5.3, and I now think that
      // binding 'A&' to 'A const &' should be an SC_QUAL_CONV, just
      // like with pointers...; moreover, I suspect that since
      // SC_LVAL_TO_RVAL and SC_QUAL_CONV have the same *rank*, I'll
      // still be able to pass 13.3.3.2 para 3 ex. 2
      xassert(ret == SC_IDENTITY);     // shouldn't have had anything added yet
      //ret |= SC_QUAL_CONV;
      
      // trying again.. 13.3.3.1.4 para 1
      ret |= SC_IDENTITY;
      
      // old code; if ultimately this solution works, I'll drop the
      // 'isReference' parameter to this function entirely...
      //ret |= SC_LVAL_TO_RVAL;
    }
    else {
      ret |= SC_QUAL_CONV;
    }
  }

  if (scv & ~dcv) {
    error("the source has some cv flag that the dest does not");
    return true;
  }

  if (!destConst && (scv != dcv)) {
    error("changed cv flags below non-const pointer");
    return true;
  }

  if (!( dcv & CV_CONST )) {
    destConst = false;
  }

  ptrCtorsStripped++;
  return false;
}


// ARR_QUAL_CONV: Regard cv flags on an array element to be cv flags
// on the array itself.  Dig down below arbitrarily many levels of
// array to find the element.
CVFlags getSrcCVFlags(Type const *src)
{
  if (src->isArrayType()) {
    ArrayType const *at = src->asArrayTypeC();
    return getSrcCVFlags(at->eltType);
  }
  else {
    return src->getCVFlags();
  }
}


// Below, each time I extract the CV flags from the 'dest' type,
// I use this function.  Whenever 'dest' names a polymorphic type,
// I pretend it has the same CV flags as the source so we don't
// get spurious mismatches.
CVFlags getDestCVFlags(Type const *dest, CVFlags srcCV)
{
  CVFlags destCV = getSrcCVFlags(dest);

  // 9/23/04: If the destination type is polymorphic, then pretend
  // the flags match.
  if (dest->isSimpleType()) {
    SimpleTypeId id = dest->asSimpleTypeC()->type;
    if (id == ST_ANY_OBJ_TYPE ||
        id == ST_ANY_NON_VOID ||
        id == ST_ANY_TYPE) {
      destCV = srcCV;
    }
  }

  return destCV;
}


bool canConvertToBaseClass(Type const *src, Type const *dest, bool &ambig)
{
  if (!dest->isCompoundType()) {
    return false;
  }
  CompoundType const *destCt = dest->asCompoundTypeC();

  CompoundType const *srcCt = NULL;
  if (src->isCompoundType()) {
    srcCt = src->asCompoundTypeC();
  }
  else if (src->isPseudoInstantiation()) {
    // (e.g. in/t0386.cc) conversion from pseudoinstantiation: can
    // convert to any of the concrete bases
    srcCt = src->asCVAtomicTypeC()->atomic->asPseudoInstantiationC()->primary;
  }
  else {
    return false;
  }

  if (srcCt->hasStrictBaseClass(destCt)) {
    ambig = !srcCt->hasUnambiguousBaseClass(destCt);
    return true;
  }

  return false;
}

    
// not sure if this is such a good idea..
bool couldBeAnything(Type const *t)
{
  // PseudoInstantiation is left out because a PI has to be
  // a class type
  return t->isSimple(ST_DEPENDENT) ||
         t->isTypeVariable() ||
         t->isDependentQType();
}


// one of the goals of this function is to *not* construct any
// intermediate Type objects; I should be able to do this computation
// without allocating, and if I can then that avoids interaction
// problems with Type annotation systems
StandardConversion getStandardConversion
  (string *errorMsg, SpecialExpr srcSpecial, Type const *src, Type const *dest,
   bool destIsReceiver)
{
  Conversion conv(errorMsg, srcSpecial, src, dest, destIsReceiver);

  // --------------- group 1 ----------------
  if (src->isReference() &&
      !src->asRvalC()->isFunctionType() &&
      !src->asRvalC()->isArrayType() &&
      !dest->isReference()) {
    conv.ret |= SC_LVAL_TO_RVAL;

    src = src->asReferenceTypeC()->atType;

    // the src type must be complete for this conversion
    if (src->isCompoundType() &&
        src->asCompoundTypeC()->forward) {
      return conv.error("type must be complete to strip '&'");
    }

    // am I supposed to check cv flags?
  }
  else if (!src->isReference() && dest->isReference()) {
    // binding an (rvalue) object to a reference

    if (!destIsReceiver) {
      // are we trying to bind to a non-const reference?  if so,
      // then we can't do it (cppstd 13.3.3.1.4 para 3)
      ReferenceType const *destPT = dest->asReferenceTypeC();
      if (!destPT->atType->isConst()) {
        // can't form the conversion
        return conv.error("attempt to bind an rvalue to a non-const reference");
      }
    }

    // strip off the destination reference
    dest = dest->asReferenceTypeC()->atType;
    
    // now, one final exception: ordinarily, there's no standard
    // conversion from C to P (where C inherits from P); but it *is*
    // legal to bind an rvalue of type C to a const reference to P
    // (cppstd 13.3.3.1.4 para 1)
    if (dest->isCompoundType() && 
        src->isCompoundType() &&
        src->asCompoundTypeC()->hasStrictBaseClass(dest->asCompoundTypeC())) {
      // TODO: ambiguous? inaccessible?
      return SC_PTR_CONV;     // "derived-to-base Conversion"
    }
  }
  else if (src->asRvalC()->isArrayType() && dest->isPointer()) {
    // 7/19/03: 'src' can be an lvalue (cppstd 4.2 para 1)

    conv.ret |= SC_ARRAY_TO_PTR;

    // note: even if we strip a reference here, we do not say it
    // is SC_LVAL_TO_RVAL (why? because I can't represent that.. and
    // I hope that that is right...)

    src = src->asRvalC()->asArrayTypeC()->eltType;
    dest = dest->asPointerTypeC()->atType;

    // do one level of qualification conversion checking
    CVFlags scv = getSrcCVFlags(src);
    CVFlags dcv = getDestCVFlags(dest, scv);

    if (srcSpecial == SE_STRINGLIT &&
        scv == CV_CONST &&
        dcv == CV_NONE) {
      // special exception of 4.2 para 2: string literals can be
      // converted to 'char*' (w/o 'const'); we'll already have
      // converted 'char const []' to 'char const *', so this just
      // adds the qualification conversion
      //
      // TODO: it might be nice to have a CCLang option to disable
      // this, so that we could get soundness at the expense of
      // compatibility with legacy code
      conv.ret |= SC_QUAL_CONV;
      scv = CV_NONE;   // avoid error in stripPtrCtor, below
    }

    if (conv.stripPtrCtor(scv, dcv))
      { return conv.ret; }
  }
  else if (src->isFunctionType() && dest->isPointerType()) {
    conv.ret |= SC_FUNC_TO_PTR;

    dest = dest->asPointerTypeC()->atType;

    CVFlags scv = getSrcCVFlags(src);
    CVFlags dcv = getDestCVFlags(dest, scv);

    if (conv.stripPtrCtor(scv, dcv))
      { return conv.ret; }
  }

  // 9/25/04: conversions to bool that must be preceded by a
  // group 1 conversion
  if (dest->isBool()) {
    // these conversions always yield 'true'.. I wonder if there
    // is a good way to take advantage of that..
    Type const *s = src->asRvalC();
    if (s->isArrayType()) {
      return conv.ret | SC_ARRAY_TO_PTR | SC_BOOL_CONV;
    }
    if (s->isFunctionType()) {
      return conv.ret | SC_FUNC_TO_PTR | SC_BOOL_CONV;
    }
  }

  // bhackett: convert (void*)0 to T*. see allowableNullPtrCastDest
  // in cc_tcheck.cc; gcc preprocessed files contain these casts,
  // and gcc can't even typecheck the files themselves.

  if (src->isPointerType() && dest->isPointerType()) {
    if (srcSpecial == SE_ZERO && src->asPointerTypeC()->atType->isVoid()) {
      return conv.ret | SC_PTR_CONV;
    }
  }

  // At this point, if the types are to be convertible, their
  // constructed type structure must be isomorphic, possibly with the
  // exception of cv flags and/or the containing class for member
  // pointers.  The next phase checks the isomorphism and verifies
  // that any difference in the cv flags is within the legal
  // variations.

  // ---------------- group 3 --------------------
  // deconstruct the type constructors until at least one of them
  // hits the leaf
  while (!src->isCVAtomicType() &&
         !dest->isCVAtomicType()) {
    if (src->getTag() != dest->getTag()) {
      // when PointerType and ReferenceType were unified, I had
      // a slightly more informative message for one case
      if (src->isPointerType() && dest->isReferenceType()) {
        return conv.error("cannot convert rvalue to lvalue");
      }
      else {
        return conv.error("different type constructors");
      }
    }

    switch (src->getTag()) {
      default: xfailure("bad type tag");

      case Type::T_POINTER:
      case Type::T_REFERENCE: {
        bool isReference = (src->isReference());

        src = src->getAtType();
        dest = dest->getAtType();

        // we look at the cv flags one level down because all of the
        // rules in cppstd talk about things like "pointer to cv T",
        // i.e. pairing the * with the cv one level down in their
        // descriptive patterns
        CVFlags srcCV = getSrcCVFlags(src);
        CVFlags destCV = getDestCVFlags(dest, srcCV);
        
        if (conv.stripPtrCtor(srcCV, destCV, isReference))
          { return conv.ret; }

        break;
      }

      case Type::T_FUNCTION: {
        // no variance is allowed whatsoever once we reach a function
        // type, which is a little odd since I'd think it would be
        // ok to pass
        //   int (*)(Base*)
        // where
        //   int (*)(Derived*)
        // is expected, but I don't see such a provision in cppstd
        //
        // 2005-04-15: Actually, 13.4p7 address this directly, and
        // explains that it is indeed illegal.
        //
        // Also, 8.3.5p4 says that exception specs are irrelevant here,
        // even though (again) there is a sound subtyping lattice.
        if (src->equals(dest)) {
          return conv.ret;
        }
        else {
          return conv.error("unequal function types");
        }
      }

      case Type::T_ARRAY: {
        // like functions, no conversions are possible on array types,
        // including (as far as I can see) converting
        //   int[3]
        // to
        //   int[]
        //
        // ARR_QUAL_CONV: A qualification conversion is possible.  The
        // element qualifier will already have been processed, so ignore
        // it during equality checking.
        if (src->equals(dest, MF_IGNORE_ELT_CV)) {
          return conv.ret;
        }
        else {
          return conv.error("unequal array types");
        }
      }

      case Type::T_POINTERTOMEMBER: {
        PointerToMemberType const *s = src->asPointerToMemberTypeC();
        PointerToMemberType const *d = dest->asPointerToMemberTypeC();

        if (s->inClass() != d->inClass()) {
          if (conv.ptrCtorsStripped == 0) {
            // opposite to first ptr ctor, we allow Base -> Derived
            if (!d->inClass()->hasUnambiguousBaseClass(s->inClass())) {
              return conv.error("src member's class is not an unambiguous "
                                "base of dest member's class");
            }
            else if (d->inClass()->hasVirtualBase(s->inClass())) {
              return conv.error("src member's class is a virtual base of "
                                "dest member's class");
            }
            else {
              // TODO: check accessibility.. this depends on the access privileges
              // of the code we're in now..

              // this is actually a group 2 conversion
              conv.ret |= SC_PTR_MEMB_CONV;
            }
          }
          else {
            // after the first ctor, variance is not allowed
            return conv.error("unequal member classes in ptr-to-member that "
                              "is not the topmost type");
          }
        }

        src = s->atType;
        dest = d->atType;

        CVFlags scv = getSrcCVFlags(src);
        CVFlags dcv = getDestCVFlags(dest, scv);

        if (conv.stripPtrCtor(scv, dcv))
          { return conv.ret; }

        // 10/08/04: (t0344.cc) For ptr-to-member where the member is
        // a function, we need to ignore the receiver parameter.  So
        // what follows is basically the T_FUNCTION case, above, but
        // with a different EqFlags passed.
        if (src->isFunctionType() && dest->isFunctionType()) {
          if (src->equals(dest, MF_IGNORE_IMPLICIT)) {
            return conv.ret;
          }
          else {
            return conv.error("unequal function types");
          }
        }

        break;
      }
    }
  }

  // ---------------- group 2 --------------

  if (couldBeAnything(src) ||
      couldBeAnything(dest)) {
    // conversion could be as good as identity (in/t0572.cc)
    return conv.ret;
  }

  // if I check equality here, will it mess anything up?
  // no, looks ok; I'm going to try folding polymorphic
  // checking into equality itself...
  // 
  // appears to work!  I'll tag the old stuff with "delete me"
  // for the moment
  if (src->equals(dest, MF_POLYMORPHIC)) {
    return conv.ret;    // identical now
  }

  if (conv.ptrCtorsStripped == 1 &&
      dest->isSimple(ST_VOID)) {
    return conv.ret | SC_PTR_CONV;      // converting T* to void*
  }

  // if both types have not arrived at CVAtomic, then they
  // are not convertible
  if (!src->isCVAtomicType() ||
      !dest->isCVAtomicType()) {
    // exception: pointer -> bool
    if (dest->isSimple(ST_BOOL) &&
        (src->isPointerType() || src->isPointerToMemberType())) {
      return conv.ret | SC_BOOL_CONV;
    }

    // exception: 0 -> (null) pointer
    if (srcSpecial == SE_ZERO) {
      if (dest->isPointerType()) {
        return conv.ret | SC_PTR_CONV;
      }
      if (dest->isPointerToMemberType()) {
        return conv.ret | SC_PTR_MEMB_CONV;
      }
    }

    if (errorMsg) {
      // if reporting, I go out of my way a bit here since I expect
      // this to be a relatively common error and I'd like to provide
      // as much information as will be useful
      if (dest->isReference()) {
        return conv.error("cannot convert rvalue to lvalue");
      }

      return conv.error(stringc
        << "different type constructors, "
        << ctorName(src->getTag()) << " vs. "
        << ctorName(dest->getTag()));
    }
    else {
      return SC_ERROR;     // for performance, don't make the string at all
    }
  }

  // now we're down to atomics; we expect equality, but ignoring cv
  // flags because they've already been handled

  CVAtomicType const *s = src->asCVAtomicTypeC();
  CVAtomicType const *d = dest->asCVAtomicTypeC();

  if (conv.ptrCtorsStripped > 0) {
    if (conv.ptrCtorsStripped == 1) {
      bool ambig = false;
      if (canConvertToBaseClass(src, dest, ambig)) {
        if (ambig) {
          return conv.error("base class is ambiguous");
        }
        // TODO: check accessibility.. this depends on the access privileges
        // of the code we're in now..
        return conv.ret | SC_PTR_CONV;      // converting Derived* to Base*
      }
    }

    // since we stripped ptrs, final type must be equal
    if (s->atomic->equals(d->atomic)) {
      return conv.ret;
    }
    else {
      // 9/25/04: (in/t0316.cc) I'm not sure where the best place to do
      // this is, in part b/c I don't know what the real rule is.  This
      // allows e.g. 'unsigned int &' to be passed where 'int const &'
      // is expected.
      if (conv.dest->isReference() &&
          conv.dest->getAtType()->isConst()) {
        // just strip the reference part of the dest; this is like binding
        // the (const) reference, which is not an explicit part of the
        // "conversion"
        return getStandardConversion(errorMsg, srcSpecial, conv.src, 
                                     conv.dest->asRvalC(), destIsReceiver);
      }

      return conv.error("incompatible atomic types");
    }
  }
  else {
    // further info on this: 13.3.3.1 para 6, excerpt:
    //   "Any difference in top-level cv-qualification is
    //    subsumed by the initialization and does not
    //    constitute a conversion."

    #if 0    // am I supposed to do any checking?
    // I'm not perfectly clear on the checking I should do for
    // the cv flags here.  lval-to-rval says that 'int const &'
    // becomes 'int' whereas 'Foo const &' becomes 'Foo const'
    if ((conv.ret & SC_LVAL_TO_RVAL) &&     // did we do lval-to-rval?
        s->atomic->isSimpleType()) {        // were we a ref to simple?
      // clear any 'const' on the source
      scv &= ~CV_CONST;
    }

    if (scv != dcv) {
      return conv.error("different cv flags (is this right?)");
    }
    #endif // 0
  }

  if (s->atomic->equals(d->atomic)) {
    return conv.ret;    // identical now
  }

  SimpleType const *srcSimple = src->isSimpleType() ? src->asSimpleTypeC() : NULL;
  SimpleType const *destSimple = dest->isSimpleType() ? dest->asSimpleTypeC() : NULL;

  if (isIntegerPromotion(s->atomic, d->atomic)) {
    return conv.ret | SC_INT_PROM;
  }

  if (srcSimple && srcSimple->type == ST_FLOAT &&
      destSimple && destSimple->type == ST_DOUBLE) {
    return conv.ret | SC_FLOAT_PROM;
  }

  // do this before checking for SC_INT_CONV, since a destination
  // type of 'bool' is explicitly excluded by 4.7 para 4
  if (isNumeric(src, srcSimple) &&
      destSimple && destSimple->type == ST_BOOL) {
    return conv.ret | SC_BOOL_CONV;
  }

  if (isIntegerNumeric(src, srcSimple) &&
      destSimple && isIntegerType(destSimple->type)) {
    return conv.ret | SC_INT_CONV;
  }

  bool srcFloat = srcSimple && isFloatType(srcSimple->type);
  bool destFloat = destSimple && isFloatType(destSimple->type);
  if (srcFloat && destFloat) {
    return conv.ret | SC_FLOAT_CONV;
  }

  if (isNumeric(src, srcSimple) &&
      isNumeric(dest, destSimple) &&
      (srcFloat || destFloat)) {     // last test required if both are enums
    return conv.ret | SC_FLOAT_INT_CONV;
  }

  // no more conversion possibilities remain; I don't print the
  // atomic kinds, because the error is based on more than just
  // the kinds; moreover, since I already know I didn't strip
  // any ptr ctors, the full types should be easy to read
  return conv.error("incompatible atomic types");
}


// This function implements Section 4.5, which contains
// implementation-determined details.  Promotions are distinguished
// from conversions in that they are preferred over conversions during
// overload resolution.  Since this distinction is implementation-
// dependent, I envision that users might replace this function with
// an implementation that better suits them.
//
// NOTE:  One way to get a conservative analysis that never silently
// chooses among potentially-ambiguous choices is to make this always
// return false.
//
// Another idea:  It would be nice to have a set of tests such that
// by running the tests one could determine what choices a given compiler
// makes, so that this function could be modified accordingly to
// imitate that behavior.
bool isIntegerPromotion(AtomicType const *src, AtomicType const *dest)
{
  bool srcSimple = src->isSimpleType();
  bool destSimple = dest->isSimpleType();

  SimpleTypeId sid = srcSimple? src->asSimpleTypeC()->type : ST_ERROR;
  SimpleTypeId did = destSimple? dest->asSimpleTypeC()->type : ST_ERROR;

  if (did == ST_INT ||
      did == ST_PROMOTED_INTEGRAL ||
      did == ST_PROMOTED_ARITHMETIC) {
    // paragraph 1: char/short -> int
    // implementation choice: I assume char is 8 bits and short
    // is 16 bits and int is 32 bits, so all map to 'int', as
    // opposed to 'unsigned int'
    if (sid == ST_CHAR ||
        sid == ST_UNSIGNED_CHAR ||
        sid == ST_SIGNED_CHAR ||
        sid == ST_SHORT_INT ||
        sid == ST_UNSIGNED_SHORT_INT) {
      return true;
    }

    // paragraph 2: wchar_t/enum -> int
    // implementation choice: I assume wchar_t and all enums fit into ints
    if (sid == ST_WCHAR_T ||
        src->isEnumType()) {
      return true;
    }

    // TODO: paragraph 3: bitfields

    // paragraph 4: bool -> int
    if (sid == ST_BOOL) {
      return true;
    }
  }

  return false;
}


Type *makeSimpleType(TypeFactory &tfac, SimpleTypeId id)
{
  return tfac.getSimpleType(id);
}

Type *getConcreteDestType(TypeFactory &tfac, Type *srcType,
                          StandardConversion sconv,
                          SimpleTypeId destPolyType)
{                 
  // move 'srcType' closer to the actual dest type according to group 1
  if (sconv & SC_LVAL_TO_RVAL) {
    srcType = srcType->getAtType();
    sconv &= ~SC_LVAL_TO_RVAL;
  }
  else {
    // I don't think any other group 1 is possible when
    // converting to a polymorphic type
    xassert(!( sconv & SC_GROUP_1_MASK ));
  }

  // group 3: I believe this is impossible too
  xassert(!( sconv & SC_GROUP_3_MASK ));

  // so now we only have group 2 to deal with
  xassert(sconv == (sconv & SC_GROUP_2_MASK));

  // if no conversions remain, we're done
  if (sconv == SC_IDENTITY) {
    return srcType;
  }

  switch (destPolyType) {
    // if this fails, the caller most likely failed to recognize
    // that it could answer its question directly
    default: xfailure("bad polymorphic type");

    // the following includes some guesswork... there are probably
    // bugs here; for now, I generally prefer to return something
    // than to fail an assertion

    case ST_PROMOTED_INTEGRAL:
      // most likely SC_INT_PROM; I only promote to ST_INT
      return makeSimpleType(tfac, ST_INT);

    case ST_PROMOTED_ARITHMETIC:
      if (sconv == SC_INT_PROM) {
        return makeSimpleType(tfac, ST_INT);
      }
      else {
        return makeSimpleType(tfac, ST_DOUBLE);
      }

    // not sure what conversions would be needed here..
    case ST_INTEGRAL:
    case ST_ARITHMETIC:
    case ST_ARITHMETIC_NON_BOOL:
      return makeSimpleType(tfac, ST_INT);

    case ST_ANY_OBJ_TYPE:
    case ST_ANY_NON_VOID:
    case ST_ANY_TYPE:
      // I really have no idea what could cause a conversion
      // here, so I will go ahead and complain
      xfailure("I don't think this is possible; conversion to very broad polymorphic type?");
      return makeSimpleType(tfac, ST_INT);    // silence warning...
  }
}

     
void getIntegerStats(SimpleTypeId id, int &length, int &uns)
{
  switch (id) {
    // bhackett: bad types can leak here if there were parse/tcheck errors.
    // default: xfailure("bad id for getIntegerLength");
    default:                      length=0; uns=0; return;

    case ST_INT:                  length=0; uns=0; return;
    case ST_UNSIGNED_INT:         length=0; uns=1; return;

    case ST_LONG_INT:             length=1; uns=0; return;
    case ST_UNSIGNED_LONG_INT:    length=1; uns=1; return;

    case ST_LONG_LONG:            length=2; uns=0; return;
    case ST_UNSIGNED_LONG_LONG:   length=2; uns=1; return;
  }
}


// implemented below
static SimpleTypeId uacHelper(SimpleTypeId leftId, SimpleTypeId rightId);

// cppstd section 5 para 9
// and C99 secton 6.3.1.8 para 1
Type *usualArithmeticConversions(TypeFactory &tfac, Type *left, Type *right)
{
  if (left->isError()) { return left; }
  if (right->isError()) { return right; }

  // if either operand is of type long double, [return] long double
  if (left->isSimple(ST_LONG_DOUBLE)) { return left; }
  if (right->isSimple(ST_LONG_DOUBLE)) { return right; }

  // similar for double
  if (left->isSimple(ST_DOUBLE)) { return left; }
  if (right->isSimple(ST_DOUBLE)) { return right; }

  // and float
  if (left->isSimple(ST_FLOAT)) { return left; }
  if (right->isSimple(ST_FLOAT)) { return right; }

  // now apply integral promotions (4.5)
  SimpleTypeId leftId = applyIntegralPromotions(left);
  SimpleTypeId rightId = applyIntegralPromotions(right);

  // conversions on SimpleTypeIds
  SimpleTypeId lubId = uacHelper(leftId, rightId);

  // package it
  return makeSimpleType(tfac, lubId);
}

SimpleTypeId usualArithmeticConversions(SimpleTypeId leftId, SimpleTypeId rightId)
{
  // same initial tests as above, but directly on the ids

  // if either operand is of type long double, [return] long double
  if (leftId == ST_LONG_DOUBLE) { return leftId; }
  if (rightId == ST_LONG_DOUBLE) { return rightId; }

  // similar for double
  if (leftId == ST_DOUBLE) { return leftId; }
  if (rightId == ST_DOUBLE) { return rightId; }

  // and float
  if (leftId == ST_FLOAT) { return leftId; }
  if (rightId == ST_FLOAT) { return rightId; }

  // now apply integral promotions (4.5)
  leftId = applyIntegralPromotions(leftId);
  rightId = applyIntegralPromotions(rightId);

  // conversions on SimpleTypeIds
  SimpleTypeId lubId = uacHelper(leftId, rightId);

  return lubId;
}

static SimpleTypeId uacHelper(SimpleTypeId leftId, SimpleTypeId rightId)
{
  // At this point, both cppstd and C99 go into gory detail
  // case-analyzing the types (which are both integral types at least
  // 'int' or bigger/wider).  However, the effect of both analyses is
  // to simply compute the least upper bound over the lattice of the
  // "all values can be represented by" relation.  This relation
  // is always an extension of the following minimal one:
  //
  //        long long       ------->    unsigned long long
  //           ^                                ^
  //           |                                |
  //          long          ------->      unsigned long
  //           ^                                ^
  //           |                                |
  //          int           ------->       unsigned int
  //
  // Additional implementation-specific edges may be added when the
  // representation ranges allow.  For example if 'long' is 64 bits
  // and 'unsigned int' is 32 bits, then there will be an edge from
  // 'unsigned int' to 'long', and that edge participates in the
  // least-upper-bound computation.  I play it conservative and
  // compute my LUB over just the minimal one displayed above.

  // mod out the length (C99 term: "conversion rank") and unsignedness
  int leftLength, leftUns;
  getIntegerStats(leftId, leftLength, leftUns);
  int rightLength, rightUns;
  getIntegerStats(rightId, rightLength, rightUns);

  // least upper bound of a product lattice
  int lubLength = max(leftLength, rightLength);
  int lubUns = max(leftUns, rightUns);

  // put them back together
  static SimpleTypeId const map[3 /*length*/][2 /*unsignedness*/] = {
    { ST_INT,           ST_UNSIGNED_INT },
    { ST_LONG_INT,      ST_UNSIGNED_LONG_INT },
    { ST_LONG_LONG,     ST_UNSIGNED_LONG_LONG }
  };
  SimpleTypeId lubId = map[lubLength][lubUns];
  
  return lubId;
}


// cppstd 4.5
SimpleTypeId applyIntegralPromotions(Type *t)
{
  // since I only promote to 'int', this is easy

  if (!t->isSimpleType()) {    // enumerations, mainly
    return ST_INT;
  }
  SimpleTypeId id = t->asSimpleTypeC()->type;
  
  return applyIntegralPromotions(id);
}

SimpleTypeId applyIntegralPromotions(SimpleTypeId id)
{
  switch (id) {
    case ST_CHAR:
    case ST_SIGNED_CHAR:
    case ST_UNSIGNED_CHAR:
    case ST_SHORT_INT:
    case ST_UNSIGNED_SHORT_INT:
    case ST_WCHAR_T:
    case ST_BOOL:
      return ST_INT;    // promote smaller integer values

    default:
      return id;        // keep everything else
  }
}


void test_getStandardConversion(
  Env &env, SpecialExpr special, Type const *src, Type const *dest,
  int expected)
{
  // run our function
  string errorMsg;
  StandardConversion actual = getStandardConversion(&errorMsg, special, src, dest);

  // turn any resulting messags into warnings, so I can see their
  // results without causing the final exit status to be nonzero
  if (actual == SC_ERROR) {
    env.warning(errorMsg);
  }

  // did the function do what we expected?
  if (actual != expected) {
    // no, explain the situation
    env.error(stringc
      << "getStandardConversion("
      << toString(special) << ", `"
      << src->toString() << "', `"
      << dest->toString() << "') yielded "
      << toString(actual) << ", but I expected "
      << toString((StandardConversion)expected));
  }
  else if (tracingSys("gSC")) {
    // make a warning to show what happened anyway
    env.warning(stringc
      << "getStandardConversion("
      << toString(special) << ", `"
      << src->toString() << "', `"
      << dest->toString() << "') yielded "
      << toString(actual));
  }
}


// ------------------- reference-relatedness ------------------
bool isReferenceRelatedTo(Type *t1, Type *t2)
{
  // ignoring toplevel cv-qualification, either t1 and t2 must be
  // the same type, or they must be classes and t1 must be a base
  // class of t2

  // this sometimes ends up with t2 being polymorphic, so it goes first
  if (t2->equals(t1, MF_IGNORE_TOP_CV | MF_POLYMORPHIC)) {
    return true;
  }
  
  // this implicitly skips toplevel cv
  if (t1->isCompoundType() &&
      t2->isCompoundType() &&
      t2->asCompoundType()->hasBaseClass(t1->asCompoundType())) {
    return true;
  }

  return false;
}


int referenceCompatibility(Type *t1, Type *t2)
{
  if (!isReferenceRelatedTo(t1, t2)) {
    return 0;      // not even related
  }

  // get the toplevel cv flags
  CVFlags cv1 = t1->getCVFlags();
  CVFlags cv2 = t2->getCVFlags();

  if (cv1 == cv2) {
    return 2;      // exact match
  }
  
  if (cv1 & cv2 == cv2) {
    // cv1 is a superset
    return 1;      // "compatible with added qualification"
  }
  
  return 0;        // not compatible
}


// EOF
