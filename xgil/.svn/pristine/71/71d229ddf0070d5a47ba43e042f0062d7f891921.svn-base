// cc_lang.h            see license.txt for copyright and terms of use
// language options that the parser (etc.) is sensitive to

// a useful reference:
//   Incompatibilities Between ISO C and ISO C++
//   David R. Tribble
//   http://david.tribble.com/text/cdiffs.htm

#ifndef CCLANG_H
#define CCLANG_H


// This type is used for options that nominally either allow or
// disallow some syntax, but can also trigger a warning.  Values of
// this type are intended to be tested like booleans in most places.
enum Bool3 {
  B3_FALSE = 0,      // syntax not allowed
  B3_TRUE = 1,       // accepted silently
  B3_WARN = 2,       // accept with a warning
};


class CCLang {
public:
  // catch-call for behaviors that are unique to C++ but aren't
  // enumerated above; these behaviors are candidates for being split
  // out as separate flags, but there currently is no need
  bool isCplusplus;

  // declare the various GNU __builtin functions; see
  // Env::addGNUBuiltins in gnu.cc
  bool declareGNUBuiltins;

  // when this is true, and the parser sees "struct Foo { ... }",
  // it will pretend it also saw "typedef struct Foo Foo;" -- i.e.,
  // the structure (or class) tag name is treated as a type name
  // by itself
  bool tagsAreTypes;

  // when true, recognize C++ keywords in input stream
  bool recognizeCppKeywords;

  // when true, every function body gets an implicit
  //   static char const __func__[] = "function-name";
  // declaration just inside the opening brace, where function-name is
  // the name of the function; this is a C99 feature (section 6.4.2.2)
  bool implicitFuncVariable;

  // behavior of gcc __FUNCTION__ and __PRETTY_FUNCTION__
  // see also
  //   http://gcc.gnu.org/onlinedocs/gcc-3.4.1/gcc/Function-Names.html
  //   http://gcc.gnu.org/onlinedocs/gcc-2.95.3/gcc_4.html#SEC101
  enum GCCFuncBehavior {
    GFB_none,              // ordinary symbols
    GFB_string,            // string literal (they concatenate!)
    GFB_variable,          // variables, like __func__
  } gccFuncBehavior;

  // when true, and we see a class declaration inside something,
  // pretend it was at toplevel scope anyway; this also applies to
  // enums, enumerators and typedefs
  //
  // dsw: I find that having boolean variables that are in the
  // negative sense is usually a mistake.  I would reverse the sense
  // of this one.
  //
  // sm: The 'no' is a little misleading.  In the 'false' case,
  // syntax reflects semantics naturally; only in the 'true' case
  // is something unusual going on.  A positive-sense name might be
  // the unwieldy 'turnApparentlyInnerClassesIntoOuterClasses'.
  bool noInnerClasses;

  // when true, an uninitialized global data object is typechecked as
  // a common symbol ("C" in the nm(1) manpage) instead of a bss
  // symbol ("B").  This means that the following is not an error:
  //   int a; int a;
  // gcc seems to operate as if this is true, whereas g++ not.
  //
  // these are the so-called "tentative" definitions of C; the flag
  // is somewhat misnamed
  bool uninitializedGlobalDataIsCommon;

  // when true, if a function has an empty parameter list then it is
  // treated as supplying no parameter information (C99 6.7.5.3 para 14)
  bool emptyParamsMeansNoInfo;

  // when true, require all array sizes to be positive; when false,
  // 0-length arrays are allowed as class/struct fields
  //
  // dsw: UPDATE: allow them anywhere; needed for linux kernel
  bool strictArraySizeRequirements;

  // when true, assume arrays with no size are of size 1 and issue a
  // warning
  //
  // TODO: This is not the proper way to handle C's rules for arrays.
  // See C99 6.9.2p2, 6.9.2e5, 6.7p7 and 6.7p16.  What we have now
  // is just a hack for the sake of expedience.
  bool assumeNoSizeArrayHasSizeOne;

  // when true, we allow overloaded function declarations (same name,
  // different signature)
  bool allowOverloading;

  // when true, to every compound type add the name of the type itself
  bool compoundSelfName;

  // when true, allow a function call to a function that has never
  // been declared, implicitly declaring the function in the global
  // scope; this is for C89 (and earlier) support
  Bool3 allowImplicitFunctionDecls;

  // when true, allow function definitions that omit any return type
  // to implicitly return 'int'.
  bool allowImplicitInt;
  
  // GNU extension: when true, allow local variable arrays to have
  // sizes that are not constant
  bool allowDynamicallySizedArrays;

  // GCC extension: when true, you can say things like 'enum Foo;' and
  // it declares that an enum called Foo will be defined later
  bool allowIncompleteEnums;

  // C language, and GNU extension for C++: allow a class to have a
  // member that has the same name as the class
  bool allowMemberWithClassName;

  // every C++ compiler I have does overload resolution of operator=
  // differently from what is specified in the standard; this flag
  // causes Elsa to do the same
  bool nonstandardAssignmentOperator;

  // permit prototypes to have mismatching exception specs if the
  // function is extern "C" (TODO: provide more documentation)
  bool allowExternCThrowMismatch;

  // allow main() to be declared/defined with an implicit 'int'
  bool allowImplicitIntForMain;

  // when true, "_Bool" is a built-in type keyword (C99)
  bool predefined_Bool;

  // when true, a function definition with 'extern' and 'inline'
  // keywords is treated like a prototype
  bool treatExternInlineAsPrototype;

  // dsw: C99 std 6.4.5p5: "For character string literals, the array
  // elements have type char...."; Cppstd 2.13.4p1: "An ordinary
  // string literal has type "array of const char" and static storage
  // duration"; But empirical results show that even in C++, gcc makes
  // string literals arrays of (nonconst) chars.
  bool stringLitCharsAreConst;

  // if the argument to a cast is an lvalue, make the cast expression
  // have lvalue type
  bool lvalueFlowsThroughCast;

  // when true, 'restrict' is a keyword
  bool restrictIsAKeyword;

  // ---- bug compatibility flags ----
  // gcc-2 bug compatibility: permit string literals to contain
  // (unescaped) newline characters in them
  bool allowNewlinesInStringLits;

  // MSVC bug compatibility: allow implicit int for operator functions
  Bool3 allowImplicitIntForOperators;

  // gcc bug compatibility: allow qualified member declarations
  Bool3 allowQualifiedMemberDeclarations;

  // gcc bug compatibility: allow typedef names to combine with
  // certain type keywords, e.g., "u32 long", in/gnu/dC0014.c;
  // eventually, once the client codes have been fixed, it would be
  // good to delete this, since it involves some extra grammar
  // productions
  Bool3 allowModifiersWithTypedefNames;

  // gcc/msvc bug/extension compatibility: allow anonymous structs;
  // see doc/anon-structs.txt
  Bool3 allowAnonymousStructs;

  // gcc-2 bug compatibility: In gcc-2, namespace "std::" is actually
  // an alias for the global scope.  This flag turns on some hacks
  // to accept some code preprocessed with gcc-2 headers.
  bool gcc2StdEqualsGlobalHacks;

  // more gcc-2 bug compat: The gcc-2 headers contain some invalid
  // syntax.  Conceptually, this flag recognizes the invalid syntax
  // and transforms it into valid syntax for Elsa.  Actually, it just
  // enables some hacks that have similar effect.
  Bool3 allowGcc2HeaderSyntax;
  
  // gcc C-mode bug compat: accept duplicate type specifier keywords
  // like 'int int'
  Bool3 allowRepeatedTypeSpecifierKeywords;
  
  // gcc C-mode bug compat: silently allow const/volatile to be
  // applied to function types via typedefs; it's meaningless
  Bool3 allowCVAppliedToFunctionTypes;

  // gcc bug compat: gcc does not enforce the rule that a definition
  // must be in a scope that encloses the declaration
  Bool3 allowDefinitionsInWrongScopes;
  
  // gcc bug compat: in C++ mode, gcc allows prototype parameters to
  // have the same name (in/gnu/bugs/gb0011.cc)
  Bool3 allowDuplicateParameterNames;
  
  // gcc bug compat: gcc does not require "template <>" is some
  // cases for explicit specializations (in/gnu/bugs/gb0012.cc)
  Bool3 allowExplicitSpecWithoutParams;
                     
private:     // funcs
  void setAllWarnings(bool enable);

public:      // funcs
  CCLang() { ANSI_C89(); }

  // set any B3_TRUE to B3_WARN
  void enableAllWarnings() { setAllWarnings(true); }

  // set any B3_WARN to B3_TRUE
  void disableAllWarnings() { setAllWarnings(false); }

  // the following are additive incremental

  // enable gcc C features
  void GNU_C_extensions();

  // enable C99 features
  void ANSI_C99_extensions();

  // enable MSVC bug compatibility
  void MSVC_bug_compatibility();

  // The predefined settings below are something of a best-effort at
  // reasonable starting configurations.  Every function below sets
  // *all* of the flags; they are not incremental.  Users are
  // encouraged to explicitly set fields after activating a predefined
  // setting to get a specific setting.

  void KandR_C();           // settings for K&R C
  void ANSI_C89();          // settings for ANSI C89
  void ANSI_C99();          // settings for ANSI C99
  void GNU_C();             // settings for GNU C
  void GNU_KandR_C();       // GNU 3.xx C + K&R compatibility
  void GNU2_KandR_C();      // GNU 2.xx C + K&R compatibility

  void ANSI_Cplusplus();    // settings for ANSI C++ 98
  void GNU_Cplusplus();     // settings for GNU C++
};

#endif // CCLANG_H
