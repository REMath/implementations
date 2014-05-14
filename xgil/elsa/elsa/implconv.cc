// implconv.cc                       see license.txt for copyright and terms of use
// code for implconv.h

#include "implconv.h"      // this module
#include "cc_env.h"        // Env
#include "variable.h"      // Variable
#include "overload.h"      // resolveOverload
#include "trace.h"         // tracingSys


// prototypes
StandardConversion tryCallCtor
  (Variable const *var, SpecialExpr special, Type const *src);



// ------------------- ImplicitConversion --------------------
char const * const ImplicitConversion::kindNames[NUM_KINDS] = {
  "IC_NONE",
  "IC_STANDARD",
  "IC_USER_DEFINED",
  "IC_ELLIPSIS",
  "IC_AMBIGUOUS"
};

void ImplicitConversion::addStdConv(StandardConversion newScs)
{
  if (kind != IC_NONE) {
    kind = IC_AMBIGUOUS;
    return;
  }

  kind = IC_STANDARD;
  scs = newScs;
}


void ImplicitConversion
  ::addUserConv(StandardConversion first, Variable *userFunc,
                StandardConversion second)
{
  if (kind != IC_NONE) {
    kind = IC_AMBIGUOUS;
    return;
  }

  kind = IC_USER_DEFINED;
  scs = first;
  user = userFunc;
  scs2 = second;
}


void ImplicitConversion::addEllipsisConv()
{
  if (kind != IC_NONE) {
    kind = IC_AMBIGUOUS;
    return;
  }

  kind = IC_ELLIPSIS;
}


Type *ImplicitConversion::getConcreteDestType
  (TypeFactory &tfac, Type *srcType, Type *destType) const
{
  // skip past the user-defined conversion, if any
  StandardConversion sconv = scs;
  if (kind == IC_USER_DEFINED) {
    srcType = user->type->asFunctionType()->retType;
    sconv = scs2;
  }

  // 2005-04-15: in/k0032.cc: if both src and dest are reference
  // types, skip that
  if (srcType->isReference() &&
      destType->isReference()) {
    Type *destAt = destType->getAtType();
    Type *srcAt = srcType->getAtType();

    Type *concrete = inner_getConcreteDestType(tfac, srcAt, destAt, sconv);
    if (concrete == destAt) {
      return destType;        // was concrete already
    }
    else {
      // must re-construct the reference part of the type
      return tfac.makeReferenceType(concrete);
    }
  }

  return inner_getConcreteDestType(tfac, srcType, destType, sconv);
}

// this function exists just so that the reference/reference case
// can use it as a subroutine ...
Type *ImplicitConversion::inner_getConcreteDestType
  (TypeFactory &tfac, Type *srcType, Type *destType, StandardConversion sconv) const
{
  if (destType->isPointer()) {
    // hmm.. operator+ has '<any obj> *'

    Type *destAtType = destType->getAtType();
    if (!destAtType->isSimpleType()) {
      return destType;      // easy
    }

    SimpleTypeId id = destAtType->asSimpleTypeC()->type;
    if (isConcreteSimpleType(id)) {
      return destType;      // also easy
    }

    // if 'destType' is a reference to a polymorphic type,
    // then this wouldn't be right ....
    srcType = srcType->asRval();

    // apply the conversion
    if (sconv == SC_ARRAY_TO_PTR) {
      srcType = tfac.makePointerType(CV_NONE,
        srcType->asArrayType()->eltType);
    }

    // anything more to do?  not sure...

    return srcType;
  }

  // these first two conditions are the same as at the top
  // of OverloadResolver::getReturnType ...

  if (!destType->isSimpleType()) {
    return destType;      // easy
  }

  SimpleTypeId id = destType->asSimpleTypeC()->type;
  if (isConcreteSimpleType(id)) {
    return destType;      // also easy
  }

  // ask the standard conversion module what type results when using
  // 'sconv' to convert from 'srcType' to the polymorphic 'destType'
  SimpleTypeId destPolyType = destType->asSimpleTypeC()->type;
  return ::getConcreteDestType(tfac, srcType, sconv, destPolyType);
}
  

string ImplicitConversion::debugString() const
{
  stringBuilder sb;
  sb << kindNames[kind];

  if (kind == IC_STANDARD || kind == IC_USER_DEFINED) {
    sb << "(" << toString(scs); 

    if (kind == IC_USER_DEFINED) {
      sb << ", " << user->name << " @ " << toString(user->loc)
         << ", " << toString(scs2);
    }

    sb << ")";
  }

  return sb;
}


// --------------------- getImplicitConversion ---------------
ImplicitConversion getImplicitConversion
  (Env &env, SpecialExpr special, Type *src, Type *dest, bool destIsReceiver)
{
  ImplicitConversion ret;

  if (src->asRval()->isGeneralizedDependent()) {
    ret.addStdConv(SC_IDENTITY);      // could be as good as this
    return ret;
  }

  // 9/25/04: conversion from template class pointer requires
  // instantiating the template class, so we can try derived-to-base
  // conversions
  if (src->asRval()->isPointerType()) {
    Type *at = src->asRval()->asPointerType()->atType;
    if (at->isCompoundType()) {
      env.ensureClassBodyInstantiated(at->asCompoundType());
    }
  }

  // check for a standard sequence
  {
    StandardConversion scs =
      getStandardConversion(NULL /*errorMsg*/, special, src, dest, destIsReceiver);
    if (scs != SC_ERROR) {
      ret.addStdConv(scs);
      return ret;
    }
  }

  // 13.3.3.1p6: derived-to-base conversion? (acts like a standard
  // conversion for overload resolution, but is not a "real" standard
  // conversion, because in actuality a constructor call is involved)
  if (dest->isCompoundType() &&
      src->asRval()->isCompoundType()) {
    CompoundType *destCt = dest->asCompoundType();
    CompoundType *srcCt = src->asRval()->asCompoundType();
    
    if (srcCt->hasBaseClass(destCt)) {
      ret.addStdConv(SC_DERIVED_TO_BASE);
      return ret;
    }
  }

  // check for a constructor to make the dest type; for this to
  // work, the dest type must be a class type or a const reference
  // to one
  if (dest->isCompoundType() ||
      (dest->asRval()->isCompoundType() &&
       dest->asRval()->isConst())) {
    CompoundType *ct = dest->asRval()->asCompoundType();
    
    // (in/t0514.cc) conversion to a template class specialization
    // requires that the specialization be instantiated
    env.ensureClassBodyInstantiated(ct);

    // get the overload set of constructors
    Variable *ctor = ct->getNamedField(env.constructorSpecialName, env);
    if (!ctor) {
      // ideally we'd have at least one ctor for every class, but I
      // think my current implementation doesn't add all of the
      // implicit constructors.. and if there are only implicit
      // constructors, they're handled specially anyway (I think),
      // so we can just disregard the possibility of using one
    }
    else {
      if (ctor->overload) {
        // multiple ctors, resolve overloading; but don't further
        // consider user-defined conversions; note that 'explicit'
        // constructors are disregarded (OF_NO_EXPLICIT)
        GrowArray<ArgumentInfo> argTypes(1);
        argTypes[0] = ArgumentInfo(special, src);
        OVERLOADINDTRACE("overloaded call to constructor " << ct->name);
        bool wasAmbig;
        ctor = resolveOverload(env, env.loc(), NULL /*errors*/,
                               OF_NO_USER | OF_NO_EXPLICIT,
                               ctor->overload->set, NULL /*finalName*/,
                               argTypes, wasAmbig);
        if (ctor) {
          // printing is now done inside 'resolveOverload'
          //TRACE("overload", "  selected constructor at " << toString(ctor->loc));
        }
        else if (wasAmbig) {
          //TRACE("overload", "  ambiguity while selecting constructor");
          ret.addAmbig();
        }
        else {
          //TRACE("overload", "  no constructor matches");
        }
      }

      if (ctor) {
        // only one ctor now.. can we call it?
        StandardConversion first = tryCallCtor(ctor, special, src);
        if (first != SC_ERROR) {
          // success
          ret.addUserConv(first, ctor, SC_IDENTITY);
        }
      }
    }
  }

  // check for a conversion function
  if (src->asRval()->isCompoundType()) {
    ImplicitConversion conv = getConversionOperator(
      env, env.loc(), NULL /*errors*/,
      src, dest);
    if (conv) {
      if (ret) {
        // there's already a constructor-based conversion, so this
        // sequence is ambiguous
        ret.addAmbig();
      }
      else {
        ret = conv;
      }
    }
  }

  return ret;
}


StandardConversion tryCallCtor
  (Variable const *var, SpecialExpr special, Type const *src)
{
  // certainly should be a function
  FunctionType *ft = var->type->asFunctionType();

  int numParams = ft->params.count();
  if (numParams == 0) {
    if (ft->acceptsVarargs()) {
      // I'm not sure about this.. there's no SC_ELLIPSIS..
      return SC_IDENTITY;
    }
    else {
      return SC_ERROR;
    }
  }

  if (numParams > 1) {
    if (ft->params.nthC(1)->value) {
      // the 2nd param has a default, which implies all params
      // after have defaults, so this is ok
    }
    else {
      return SC_ERROR;     // requires at least 2 arguments
    }
  }
  
  Variable const *param = ft->params.firstC();
  return getStandardConversion(NULL /*errorMsg*/, special, src, param->type);
}


// ----------------- test_getImplicitConversion ----------------
int getLine(SourceLoc loc)
{
  return sourceLocManager->getLine(loc);
}


bool matchesExpectation(ImplicitConversion const &actual,
  int expectedKind, int expectedSCS, int expectedUserLine, int expectedSCS2)
{
  if (expectedKind != actual.kind) return false;

  if (actual.kind == ImplicitConversion::IC_STANDARD) {
    return actual.scs == expectedSCS;
  }

  if (actual.kind == ImplicitConversion::IC_USER_DEFINED) {
    int actualLine = getLine(actual.user->loc);
    return actual.scs == expectedSCS &&
           actualLine == expectedUserLine &&
           actual.scs2 == expectedSCS2;
  }

  // other kinds are equal without further checking
  return true;
}


void test_getImplicitConversion(
  Env &env, SpecialExpr special, Type *src, Type *dest,
  int expectedKind, int expectedSCS, int expectedUserLine, int expectedSCS2)
{
  // grab existing error messages
  ErrorList existing;
  existing.takeMessages(env.errors);

  // run our function
  ImplicitConversion actual = getImplicitConversion(env, special, src, dest);

  // turn any resulting messags into warnings, so I can see their
  // results without causing the final exit status to be nonzero
  env.errors.markAllAsWarnings();
  
  // put the old messages back
  env.errors.takeMessages(existing);

  // did it behave as expected?
  bool matches = matchesExpectation(actual, expectedKind, expectedSCS,
                                            expectedUserLine, expectedSCS2);
  if (!matches || tracingSys("gIC")) {
    // construct a description of the actual result
    stringBuilder actualDesc;
    actualDesc << ImplicitConversion::kindNames[actual.kind];
    if (actual.kind == ImplicitConversion::IC_STANDARD ||
        actual.kind == ImplicitConversion::IC_USER_DEFINED) {
      actualDesc << "(" << toString(actual.scs);
      if (actual.kind == ImplicitConversion::IC_USER_DEFINED) {
        actualDesc << ", " << getLine(actual.user->loc)
                   << ", " << toString(actual.scs2);
      }
      actualDesc << ")";
    }

    // construct a description of the call site
    stringBuilder callDesc;
    callDesc << "getImplicitConversion("
             << toString(special) << ", `"
             << src->toString() << "', `"
             << dest->toString() << "')";

    if (!matches) {
      // construct a description of the expected result
      stringBuilder expectedDesc;
      xassert((unsigned)expectedKind <= (unsigned)ImplicitConversion::NUM_KINDS);
      expectedDesc << ImplicitConversion::kindNames[expectedKind];
      if (expectedKind == ImplicitConversion::IC_STANDARD ||
          expectedKind == ImplicitConversion::IC_USER_DEFINED) {
        expectedDesc << "(" << toString((StandardConversion)expectedSCS);
        if (expectedKind == ImplicitConversion::IC_USER_DEFINED) {
          expectedDesc << ", " << expectedUserLine
                       << ", " << toString((StandardConversion)expectedSCS2);
        }
        expectedDesc << ")";
      }

      env.error(stringc
        << callDesc << " yielded " << actualDesc
        << ", but I expected " << expectedDesc);
    }
    else {
      env.warning(stringc << callDesc << " yielded " << actualDesc);
    }
  }
}


// EOF
