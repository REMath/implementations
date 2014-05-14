// cc_lang.cc            see license.txt for copyright and terms of use
// code for cc_lang.h

#include "cc_lang.h"     // this module

#include <string.h>      // memset


static void setWarning(Bool3 &b, bool enable)
{
  if (enable) {
    if (b == B3_TRUE) {
      b = B3_WARN;       // accept with warning
    }
  }
  else {
    if (b == B3_WARN) {
      b = B3_TRUE;       // accept silently
    }
  }
}

void CCLang::setAllWarnings(bool enable)
{
  setWarning(allowImplicitFunctionDecls, enable);
  setWarning(allowImplicitIntForOperators, enable);
  setWarning(allowQualifiedMemberDeclarations, enable);
  setWarning(allowModifiersWithTypedefNames, enable);
  setWarning(allowAnonymousStructs, enable);
  setWarning(allowGcc2HeaderSyntax, enable);
  setWarning(allowRepeatedTypeSpecifierKeywords, enable);
  setWarning(allowCVAppliedToFunctionTypes, enable);
  setWarning(allowDefinitionsInWrongScopes, enable);
  setWarning(allowDuplicateParameterNames, enable);
  setWarning(allowExplicitSpecWithoutParams, enable);
}


// ---------------------- ANSI and K&R C ----------------------
void CCLang::ANSI_C89()
{
  // just in case I forget to initialize something....
  memset(this, 0, sizeof(*this));

  isCplusplus = false;
  declareGNUBuiltins = false;

  tagsAreTypes = false;
  recognizeCppKeywords = false;
  implicitFuncVariable = false;
  gccFuncBehavior = GFB_none;
  noInnerClasses = true;
  uninitializedGlobalDataIsCommon = true;
  emptyParamsMeansNoInfo = true;
  strictArraySizeRequirements = false;
  assumeNoSizeArrayHasSizeOne = false;
  allowOverloading = false;
  compoundSelfName = false;
  allowImplicitFunctionDecls = B3_TRUE;        // C89 does not require prototypes
  allowImplicitInt = true;
  allowDynamicallySizedArrays = false;
  allowIncompleteEnums = false;
  allowMemberWithClassName = true;
  nonstandardAssignmentOperator = false;
  allowExternCThrowMismatch = true;
  allowImplicitIntForMain = false;
  predefined_Bool = false;

  treatExternInlineAsPrototype = false;
  stringLitCharsAreConst = false; // Didn't check C89; C99 says they are non-const

  // C99 spec: Section 6.5.4, footnote 85: "A cast does not yield an lvalue".
  lvalueFlowsThroughCast = false;

  restrictIsAKeyword = false;

  allowNewlinesInStringLits = false;
  allowImplicitIntForOperators = B3_FALSE;
  allowQualifiedMemberDeclarations = B3_FALSE;
  allowModifiersWithTypedefNames = B3_FALSE;
  allowAnonymousStructs = B3_FALSE;

  gcc2StdEqualsGlobalHacks = false;
  allowGcc2HeaderSyntax = B3_FALSE;
  allowRepeatedTypeSpecifierKeywords = B3_FALSE;
  allowCVAppliedToFunctionTypes = B3_FALSE;
  allowDefinitionsInWrongScopes = B3_FALSE;
  allowDuplicateParameterNames = B3_FALSE;
  allowExplicitSpecWithoutParams = B3_FALSE;
}

void CCLang::KandR_C()
{
  ANSI_C89();

  allowImplicitInt = true;
}

void CCLang::ANSI_C99_extensions()
{
  implicitFuncVariable = true;
  predefined_Bool = true;
  restrictIsAKeyword = true;
}

void CCLang::ANSI_C99()
{
  ANSI_C89();

  // new features
  ANSI_C99_extensions();

  // removed C89 features
  allowImplicitInt = false;
  allowImplicitFunctionDecls = B3_FALSE;
}


// ------------------------ GNU C ------------------------
void CCLang::GNU_C_extensions()
{
  gccFuncBehavior = GFB_string;
  allowDynamicallySizedArrays = true;
  assumeNoSizeArrayHasSizeOne = true;
  treatExternInlineAsPrototype = true;
  declareGNUBuiltins = true;

  // http://gcc.gnu.org/onlinedocs/gcc-3.1/gcc/Lvalues.html
  lvalueFlowsThroughCast = true;

  allowNewlinesInStringLits = true;

  // http://gcc.gnu.org/onlinedocs/gcc-3.1/gcc/Incomplete-Enums.html
  allowIncompleteEnums = true;

  allowModifiersWithTypedefNames = B3_TRUE;
  allowAnonymousStructs = B3_TRUE;
  allowRepeatedTypeSpecifierKeywords = B3_TRUE;
  allowCVAppliedToFunctionTypes = B3_TRUE;
}

void CCLang::GNU_C()
{
  ANSI_C89();

  ANSI_C99_extensions();
  GNU_C_extensions();
}

void CCLang::GNU_KandR_C()
{
  KandR_C();

  GNU_C_extensions();

  // this seems wrong, but Oink's tests want it this way...
  ANSI_C99_extensions();
}

void CCLang::GNU2_KandR_C()
{
  GNU_KandR_C();

  // dsw: seems to not be true for gcc 2.96 at least
  predefined_Bool = false;
}


// ---------------------------- C++ ----------------------------
void CCLang::ANSI_Cplusplus()
{
  // just in case...
  memset(this, 0, sizeof(*this));

  isCplusplus = true;
  declareGNUBuiltins = false;

  tagsAreTypes = true;
  recognizeCppKeywords = true;
  implicitFuncVariable = false;
  gccFuncBehavior = GFB_none;
  noInnerClasses = false;
  uninitializedGlobalDataIsCommon = false;
  emptyParamsMeansNoInfo = false;

  strictArraySizeRequirements = true;
  assumeNoSizeArrayHasSizeOne = false;

  allowOverloading = true;
  compoundSelfName = true;

  allowImplicitFunctionDecls = B3_FALSE;
  allowImplicitInt = false;
  allowDynamicallySizedArrays = false;
  allowIncompleteEnums = false;
  allowMemberWithClassName = false;

  // indeed this is nonstandard but everyone seems to do it this way ...
  nonstandardAssignmentOperator = true;

  allowExternCThrowMismatch = false;
  allowImplicitIntForMain = false;

  predefined_Bool = false;
  treatExternInlineAsPrototype = false;
  stringLitCharsAreConst = true; // Cppstd says they are const.
  lvalueFlowsThroughCast = false;
  restrictIsAKeyword = false;

  allowNewlinesInStringLits = false;
  allowImplicitIntForOperators = B3_FALSE;
  allowQualifiedMemberDeclarations = B3_FALSE;
  allowModifiersWithTypedefNames = B3_FALSE;
  allowAnonymousStructs = B3_FALSE;

  gcc2StdEqualsGlobalHacks = false;
  allowGcc2HeaderSyntax = B3_FALSE;
  allowRepeatedTypeSpecifierKeywords = B3_FALSE;
  allowCVAppliedToFunctionTypes = B3_FALSE;
  allowDefinitionsInWrongScopes = B3_FALSE;
  allowDuplicateParameterNames = B3_FALSE;
  allowExplicitSpecWithoutParams = B3_FALSE;
}

void CCLang::GNU_Cplusplus()
{
  ANSI_Cplusplus();

  implicitFuncVariable = true;
  gccFuncBehavior = GFB_variable;

  // is this really right?  Oink tests it like it is ...
  allowDynamicallySizedArrays = true;
  strictArraySizeRequirements = false;

  allowMemberWithClassName = true;
  allowExternCThrowMismatch = true;
  allowImplicitIntForMain = true;

  declareGNUBuiltins = true;

  allowQualifiedMemberDeclarations = B3_TRUE;
  allowAnonymousStructs = B3_TRUE;

  gcc2StdEqualsGlobalHacks = true;
  allowGcc2HeaderSyntax = B3_TRUE;
  allowDefinitionsInWrongScopes = B3_TRUE;
  allowDuplicateParameterNames = B3_TRUE;
  allowExplicitSpecWithoutParams = B3_TRUE;
}


// -------------------------- MSVC ---------------------
void CCLang::MSVC_bug_compatibility()
{
  allowImplicitIntForOperators = B3_TRUE;
  allowAnonymousStructs = B3_TRUE;
}


// EOF
