// gnu.cc
// parse, tcheck and print routines for gnu.ast/gnu.gr extensions

#include "generic_aux.h"      // C++ AST, and genericPrintAmbiguities, etc.
#include "cc_env.h"           // Env
#include "cc_print.h"         // olayer, PrintEnv
#include "generic_amb.h"      // resolveAmbiguity, etc.
#include "stdconv.h"          // usualArithmeticConversions
#include "astvisit.h"         // ASTVisitorEx
#include <string.h>           // strcmp

// parsing utility functions for __builtin_offsetof

// make the expression to use for a __builtin_offsetof(type,fields) use.
// this is special because its first argument is a type and second is a
// field or index sequence. instead of making an expression for this,
// convert it to its equivalent: (unsigned)&(((type*)0)->fields)

// convert ((type*)0, fields) to (((type*)0)->fields)
Expression* make_OffsetOfArrow(Expression *zero_cast, Expression *expr)
{
  if (E_variable *nexpr = expr->ifE_variable())
    return new E_arrow(zero_cast, nexpr->name);

  if (E_fieldAcc *nexpr = expr->ifE_fieldAcc()) {
    Expression *base = make_OffsetOfArrow(zero_cast, nexpr->obj);
    if (base == NULL)
      return NULL;

    return new E_fieldAcc(base, nexpr->fieldName);
  }

  if (E_binary *nexpr = expr->ifE_binary()) {
    if (nexpr->op == BIN_BRACKETS) {
      Expression *base = make_OffsetOfArrow(zero_cast, nexpr->e1);
      if (base == NULL)
        return NULL;

      return new E_binary(base, nexpr->op, nexpr->e2);
    }
  }

  return NULL;
}

// convert (type, fields) to (unsigned)&(((type*)0)->fields)
Expression* make_OffsetOf(StringTable &str, SourceLoc loc,
                          ASTTypeId *type, Expression *expr)
{
  // make expression for "0"
  Expression *zero = new E_intLit(str("0"));

  // make type for "(type*)"
  IDeclarator *pidecl = new D_pointer(loc, CV_NONE, type->decl->decl);
  Declarator *pdecl = new Declarator(pidecl, NULL);
  ASTTypeId *ptype = new ASTTypeId(type->spec, pdecl);

  // make expression for ((type*)0)
  Expression *zero_cast = new E_cast(ptype, zero);

  // make expression for ((type*)0)->fields
  Expression *arrow = make_OffsetOfArrow(zero_cast, expr);
  if (arrow == NULL)
    return NULL;

  // make expression for &((type*)0)->fields
  Expression *addr = new E_addrOf(arrow);

  TypeSpecifier *itspec = new TS_simple(loc, loc, ST_UNSIGNED_INT);
  Declarator *idecl = new Declarator(new D_name(loc, NULL), NULL);
  ASTTypeId *itype = new ASTTypeId(itspec, idecl);

  return new E_cast(itype, addr);
}



// fwd in this file
SimpleTypeId constructFloatingType(int prec, int axis);


// --------------------------- Env ---------------------------------
// Caveat: All of the uses of GNU builtin functions arise from
// preprocessing with the gcc compiler's headers.  Strictly speaking,
// this is inappropriate, as Elsa is a different implementation and
// has its own compiler-specific headers (in the include/ directory).
// But in practice people don't often seem to be willing to adjust
// their build process enough to actually use Elsa's headers, and
// insist on using the gcc headers since that's what (e.g.) gcc -E
// finds by default.  Therefore Elsa makes a best-effort attempt to
// accept the resulting files, even though they are gcc-specific (and
// sometimes specific to a particular *version* of gcc).  This
// function is part of that effort.
//
// See  http://gcc.gnu.org/onlinedocs/gcc-3.1/gcc/Other-Builtins.html
// also http://gcc.gnu.org/onlinedocs/gcc-3.4.3/gcc/Other-Builtins.html
void Env::addGNUBuiltins()
{
  Type *t_void = getSimpleType(ST_VOID);
//    Type *t_voidconst = getSimpleType(SL_INIT, ST_VOID, CV_CONST);
  Type *t_voidptr = makePtrType(t_void);
//    Type *t_voidconstptr = makePtrType(SL_INIT, t_voidconst);

  Type *t_int = getSimpleType(ST_INT);
  Type *t_unsigned_int = getSimpleType(ST_UNSIGNED_INT);
  Type *t_char = getSimpleType(ST_CHAR);
  Type *t_charconst = getSimpleType(ST_CHAR, CV_CONST);
  Type *t_charptr = makePtrType(t_char);
  Type *t_charconstptr = makePtrType(t_charconst);

  // dsw: This is a form, not a function, since it takes an expression
  // AST node as an argument; however, I need a function that takes no
  // args as a placeholder for it sometimes.
  var__builtin_constant_p = declareSpecialFunction("__builtin_constant_p");

  // typedef void *__builtin_va_list;
  Variable *var__builtin_va_list =
    makeVariable(SL_INIT, str("__builtin_va_list"),
                 t_voidptr, DF_TYPEDEF | DF_BUILTIN | DF_GLOBAL);
  addVariable(var__builtin_va_list);

  // void __builtin_stdarg_start(__builtin_va_list __list, char const *__format);
  // trying this instead:
  // void __builtin_stdarg_start(__builtin_va_list __list, void const *__format);
  // nope; see in/d0120.cc.  It doesn't work if the arg to '__format' is an int.
  // ironically, making it vararg does work
  declareFunction1arg(t_void, "__builtin_stdarg_start",
                      var__builtin_va_list->type, "__list",
//                        t_charconstptr, "__format",
//                        t_voidconstptr, "__format",
                      FF_VARARGS, NULL);

  // void __builtin_va_start(__builtin_va_list __list, ...);
  declareFunction1arg(t_void, "__builtin_va_start",
                      var__builtin_va_list->type, "__list",
                      FF_VARARGS, NULL);

  // void __builtin_va_copy(__builtin_va_list dest, __builtin_va_list src);
  declareFunction2arg(t_void, "__builtin_va_copy",
                      var__builtin_va_list->type, "dest",
                      var__builtin_va_list->type, "src",
                      FF_NONE, NULL);

  // void __builtin_va_end(__builtin_va_list __list);
  declareFunction1arg(t_void, "__builtin_va_end",
                      var__builtin_va_list->type, "__list");

  // void *__builtin_alloca(unsigned int __len);
  declareFunction1arg(t_voidptr, "__builtin_alloca",
                      t_unsigned_int, "__len");

  // char *__builtin_strchr(char const *str, int ch);
  declareFunction2arg(t_charptr, "__builtin_strchr",
                      t_charconstptr, "str",
                      t_int, "ch",
                      FF_NONE, NULL);

  // char *__builtin_strpbrk(char const *str, char const *accept);
  declareFunction2arg(t_charptr, "__builtin_strpbrk",
                      t_charconstptr, "str",
                      t_charconstptr, "accept",
                      FF_NONE, NULL);

  // char *__builtin_strchr(char const *str, int ch);
  declareFunction2arg(t_charptr, "__builtin_strrchr",
                      t_charconstptr, "str",
                      t_int, "ch",
                      FF_NONE, NULL);

  // char *__builtin_strstr(char const *haystack, char const *needle);
  declareFunction2arg(t_charptr, "__builtin_strstr",
                      t_charconstptr, "haystack",
                      t_charconstptr, "needle",
                      FF_NONE, NULL);

  // we made some attempts to get accurate prototypes for the above
  // functions, but at some point just started using "int ()(...)"
  // as the type; the set below all get this generic type

  static char const * const arr[] = {
    // ------------------------------------------------
    // group 1: "Outside strict ISO C mode ..."

    // this set is from the 3.1 list
    //"alloca",              // prototyped above
    "bcmp",
    "bzero",
    "index",
    "rindex",
    "ffs",
    "fputs_unlocked",
    "printf_unlocked",
    "fprintf_unlocked",

    // this set is from the 3.4.3 list; the commented lines are
    // either prototyped above or in the 3.1 list
    "_exit",
    //"alloca",
    //"bcmp",
    //"bzero",
    "dcgettext",
    "dgettext",
    "dremf",
    "dreml",
    "drem",
    "exp10f",
    "exp10l",
    "exp10",
    "ffsll",
    "ffsl",
    //"ffs",
    //"fprintf_unlocked",
    //"fputs_unlocked",
    "gammaf",
    "gammal",
    "gamma",
    "gettext",
    //"index",
    "j0f",
    "j0l",
    "j0",
    "j1f",
    "j1l",
    "j1",
    "jnf",
    "jnl",
    "jn",
    "mempcpy",
    "pow10f",
    "pow10l",
    "pow10",
    //"printf_unlocked",
    //"rindex",
    "scalbf",
    "scalbl",
    "scalb",
    "significandf",
    "significandl",
    "significand",
    "sincosf",
    "sincosl",
    "sincos",
    "stpcpy",
    "strdup",
    "strfmon",
    "y0f",
    "y0l",
    "y0",
    "y1f",
    "y1l",
    "y1",
    "ynf",
    "ynl",
    "yn",

    // ------------------------------------------------
    // group 2: "The ISO C99 functions ..."

    // this is the 3.1 list
    "conj",
    "conjf",
    "conjl",
    "creal",
    "crealf",
    "creall",
    "cimag",
    "cimagf",
    "cimagl",
    "llabs",
    "imaxabs",

    // this is the 3.4.3 list, with those from 3.1 commented
    "_Exit",
    "acoshf",
    "acoshl",
    "acosh",
    "asinhf",
    "asinhl",
    "asinh",
    "atanhf",
    "atanhl",
    "atanh",
    "cabsf",
    "cabsl",
    "cabs",
    "cacosf",
    "cacoshf",
    "cacoshl",
    "cacosh",
    "cacosl",
    "cacos",
    "cargf",
    "cargl",
    "carg",
    "casinf",
    "casinhf",
    "casinhl",
    "casinh",
    "casinl",
    "casin",
    "catanf",
    "catanhf",
    "catanhl",
    "catanh",
    "catanl",
    "catan",
    "cbrtf",
    "cbrtl",
    "cbrt",
    "ccosf",
    "ccoshf",
    "ccoshl",
    "ccosh",
    "ccosl",
    "ccos",
    "cexpf",
    "cexpl",
    "cexp",
    //"cimagf",
    //"cimagl",
    //"cimag",
    //"conjf",
    //"conjl",
    //"conj",
    "copysignf",
    "copysignl",
    "copysign",
    "cpowf",
    "cpowl",
    "cpow",
    "cprojf",
    "cprojl",
    "cproj",
    //"crealf",
    //"creall",
    //"creal",
    "csinf",
    "csinhf",
    "csinhl",
    "csinh",
    "csinl",
    "csin",
    "csqrtf",
    "csqrtl",
    "csqrt",
    "ctanf",
    "ctanhf",
    "ctanhl",
    "ctanh",
    "ctanl",
    "ctan",
    "erfcf",
    "erfcl",
    "erfc",
    "erff",
    "erfl",
    "erf",
    "exp2f",
    "exp2l",
    "exp2",
    "expm1f",
    "expm1l",
    "expm1",
    "fdimf",
    "fdiml",
    "fdim",
    "fmaf",
    "fmal",
    "fmaxf",
    "fmaxl",
    "fmax",
    "fma",
    "fminf",
    "fminl",
    "fmin",
    "hypotf",
    "hypotl",
    "hypot",
    "ilogbf",
    "ilogbl",
    "ilogb",
    //"imaxabs",
    "lgammaf",
    "lgammal",
    "lgamma",
    //"llabs",
    "llrintf",
    "llrintl",
    "llrint",
    "llroundf",
    "llroundl",
    "llround",
    "log1pf",
    "log1pl",
    "log1p",
    "log2f",
    "log2l",
    "log2",
    "logbf",
    "logbl",
    "logb",
    "lrintf",
    "lrintl",
    "lrint",
    "lroundf",
    "lroundl",
    "lround",
    "nearbyintf",
    "nearbyintl",
    "nearbyint",
    "nextafterf",
    "nextafterl",
    "nextafter",
    "nexttowardf",
    "nexttowardl",
    "nexttoward",
    "remainderf",
    "remainderl",
    "remainder",
    "remquof",
    "remquol",
    "remquo",
    "rintf",
    "rintl",
    "rint",
    "roundf",
    "roundl",
    "round",
    "scalblnf",
    "scalblnl",
    "scalbln",
    "scalbnf",
    "scalbnl",
    "scalbn",
    "snprintf",
    "tgammaf",
    "tgammal",
    "tgamma",
    "truncf",
    "truncl",
    "trunc",
    "vfscanf",
    "vscanf",
    "vsnprintf",
    "vsscanf",

    // ------------------------------------------------
    // group 3: "There are also built-in versions of the ISO C99 functions ..."
    
    // 3.1 list
    "cosf",
    "cosl",
    "fabsf",
    "fabsl",
    "sinf",
    "sinl",
    "sqrtf",
    "sqrtl",

    // 3.4.3 list with 3.1 elements commented
    "acosf",
    "acosl",
    "asinf",
    "asinl",
    "atan2f",
    "atan2l",
    "atanf",
    "atanl",
    "ceilf",
    "ceill",
    //"cosf",
    "coshf",
    "coshl",
    //"cosl",
    "expf",
    "expl",
    //"fabsf",
    //"fabsl",
    "floorf",
    "floorl",
    "fmodf",
    "fmodl",
    "frexpf",
    "frexpl",
    "ldexpf",
    "ldexpl",
    "log10f",
    "log10l",
    "logf",
    "logl",
    "modfl",
    "modf",
    "powf",
    "powl",
    //"sinf",
    "sinhf",
    "sinhl",
    //"sinl",
    //"sqrtf",
    //"sqrtl",
    "tanf",
    "tanhf",
    "tanhl",
    "tanl",
    
    // gcc-3.4.3 seems to have this, though it is not documented
    "modff",
    
    // same for these
    "huge_val",
    "huge_valf",
    "huge_vall",
    "nan",

    // ------------------------------------------------
    // group 4: "The ISO C90 functions ..."
    
    // this is the 3.1 list, with things prototyped above commented
    "abs",
    "cos",
    "fabs",
    "fprintf",
    "fputs",
    "labs",
    "memcmp",
    "memcpy",
    "memmove",
    "memchr",
    "memset",
    "printf",
    "sin",
    "sqrt",
    "strcat",
    //"strchr",
    "strcmp",
    "strcpy",
    "strcspn",
    "strlen",
    "strncat",
    "strncmp",
    "strncpy",
    //"strpbrk",
    //"strrchr",
    "strspn",
    //"strstr",

    // this is the 3.4.3 list, with things either prototyped above or
    // in the 3.1 list commented
    "abort",
    //"abs",
    "acos",
    "asin",
    "atan2",
    "atan",
    "calloc",
    "ceil",
    "cosh",
    //"cos",
    "exit",
    "exp",
    //"fabs",
    "floor",
    "fmod",
    //"fprintf",
    //"fputs",
    "frexp",
    "fscanf",
    //"labs",
    "ldexp",
    "log10",
    "log",
    "malloc",
    //"memcmp",
    //"memcpy",
    //"memset",
    "modf",
    "pow",
    //"printf",
    "putchar",
    "puts",
    "scanf",
    "sinh",
    //"sin",
    "snprintf",
    "sprintf",
    //"sqrt",
    "sscanf",
    //"strcat",
    //"strchr",
    //"strcmp",
    //"strcpy",
    //"strcspn",
    //"strlen",
    //"strncat",
    //"strncmp",
    //"strncpy",
    //"strpbrk",
    //"strrchr",
    //"strspn",
    //"strstr",
    "tanh",
    "tan",
    "vfprintf",
    "vprintf",
    "vsprintf",

    // ------------------------------------------------
    // group 5: "... ISO C99 floating point comparison macros ..."

    // this is the 3.1 list, which is identical to the 3.4.3 list
    "isgreater",
    "isgreaterequal",
    "isless",
    "islessequal",
    "islessgreater",
    "isunordered",

    // ------------------------------------------------
    // group 6: miscellaneous compiler interrogations/hints

    // constant_p: implemented elsewhere
    // expect: implemented elsewhere
    "prefetch",
    "object_size",

    // these do stuff but depend on compiler interrogations.
    "memcpy_chk",
    "memmove_chk",
    "__memcpy_chk",
    "__memset_chk",
    "__memmove_chk",
    "__strcpy_chk",
    "__strcat_chk",
    "__strncpy_chk",
    "__strncat_chk",
    "__mempcpy_chk",
    "__stpcpy_chk",
    "__sprintf_chk",
    "__vsprintf_chk",
    "__snprintf_chk",
    "__vsnprintf_chk",

    // ------------------------------------------------
    // group 7: low-level arithmetic stuff

    // full prototypes:
    //   float __builtin_nanf (const char *str);
    //   long double __builtin_nanl (const char *str);
    //   double __builtin_nans (const char *str);
    //   float __builtin_nansf (const char *str);
    //   long double __builtin_nansl (const char *str);
    //   int __builtin_ffs (unsigned int x);
    //   int __builtin_clz (unsigned int x);
    //   int __builtin_ctz (unsigned int x);
    //   int __builtin_popcount (unsigned int x);
    //   int __builtin_parity (unsigned int x);
    //   int __builtin_ffsl (unsigned long);
    //   int __builtin_clzl (unsigned long);
    //   int __builtin_ctzl (unsigned long);
    //   int __builtin_popcountl (unsigned long);
    //   int __builtin_parityl (unsigned long);
    //   int __builtin_ffsll (unsigned long long);
    //   int __builtin_clzll (unsigned long long);
    //   int __builtin_ctzll (unsigned long long);
    //   int __builtin_popcountll (unsigned long long);
    //   int __builtin_parityll (unsigned long long);

    // just the names, but those that appear above are commented
    "nanf",
    "nanl",
    "nans",
    "nansf",
    "nansl",
    //"ffs",
    "clz",
    "ctz",
    "popcount",
    "parity",
    //"ffsl",
    "clzl",
    "ctzl",
    "popcountl",
    "parityl",
    //"ffsll",
    "clzll",
    "ctzll",
    "popcountll",
    "parityll",
  };

  for (int i=0; i < TABLESIZE(arr); i++) {
    makeImplicitDeclFuncVar(str(stringc << "__builtin_" << arr[i]));
  }

  // initialize 'complexComponentFields'  
  for (int axis=0; axis<=1; axis++) {
    for (int prec=0; prec<=2; prec++) {                                 
      StringRef n = axis==0? string_realSelector : string_imagSelector;
      Type *t = env.getSimpleType(constructFloatingType(prec, axis));
      Variable *v = makeVariable(SL_INIT, n, t, DF_BUILTIN | DF_MEMBER);
      complexComponentFields[axis][prec] = v;
    }
  }
}


// -------------------- tcheck --------------------
ASTTypeof *ASTTypeof::tcheck(Env &env, DeclFlags dflags)
{
  if (!ambiguity) {
    mid_tcheck(env, dflags);
    return this;
  }
  
  return resolveAmbiguity(this, env, "ASTTypeof", false /*priority*/, dflags);
}

void ASTTypeof::mid_tcheck(Env &env, DeclFlags &dflags)
{
  type = itcheck(env, dflags);
}


Type *TS_typeof_expr::itcheck(Env &env, DeclFlags dflags)
{
  // FIX: dflags discarded?
  expr->tcheck(env);
  // FIX: check the asRval(); A use in kernel suggests it should be
  // there as otherwise you get "error: cannot create a pointer to a
  // reference" when used to specify the type in a declarator that
  // comes from a de-reference (which yeilds a reference).
  return expr->getType()->asRval();
}


Type *TS_typeof_type::itcheck(Env &env, DeclFlags dflags)
{
  // bhackett: pass the dflags on when we are checking the type.
  // if this is in a typedef or typeof then it is OK if the type is incomplete.
  ASTTypeId::Tcheck tc(dflags, DC_TS_TYPEOF_TYPE);
  atype = atype->tcheck(env, tc);
  Type *t = atype->getType();
  return t;
}


Type *TS_typeof::itcheck(Env &env, DeclFlags dflags)
{
  atype = atype->tcheck(env, dflags);
  return atype->type;
}


void S_function::itcheck(Env &env)
{
  env.setLoc(loc);
  f->tcheck(env);
}


void S_rangeCase::itcheck(Env &env)
{
  exprLo->tcheck(env, exprLo);
  exprHi->tcheck(env, exprHi);
  s = s->tcheck(env);

  // compute case label values
  exprLo->constEval(env, labelValLo);
  exprHi->constEval(env, labelValHi);
}

void S_computedGoto::itcheck(Env &env)
{
  target->tcheck(env, target);

  // The GCC manual seems to imply it wants 'target' to have type
  // 'void*'.  It seems pointless to specifically require void* as
  // opposed to some other pointer type, since any other pointer type
  // can be implicitly converted to void*.  Even so, EDG does in fact
  // enforce that the arg is exactly void*.  GCC itself does not
  // appear to enforce any restrictions on the type (!).
  Type *t = target->type->asRval();
  if (!t->isPointer()) {
    env.error(t, stringc
      << "type of expression in computed goto must be a pointer, not `"
      << t->toString() << "'");
  }
}


Type *E_compoundLit::itcheck_x(Env &env, Expression *&replacement)
{
  ASTTypeId::Tcheck tc(DF_NONE, DC_E_COMPOUNDLIT);

  // typechedk the type only once, and isolated from ambiguities
  if (!tcheckedType) {
    InstantiationContextIsolator isolate(env, env.loc());
    tcheckedType = true;

    stype = stype->tcheck(env, tc);
  }

  init->tcheck(env, stype->getType());

  // dsw: Scott says: "The gcc manual says nothing about whether a
  // compound literal is an lvalue.  But, compound literals are now
  // part of C99 (6.5.2.5), which says they are indeed lvalues (but
  // says nothing about being const)."
  Type *t0 = stype->getType();
  Type *t1 = env.computeArraySizeFromCompoundInit(env.loc(), t0, t0, init);
  return env.makeReferenceType(t1);
  // TODO: check that the cast (literal) makes sense
}


Type *E___builtin_constant_p::itcheck_x(Env &env, Expression *&replacement)
{
  expr->tcheck(env, expr);

//    // TODO: this will fail an assertion if someone asks for the
//    // size of a variable of template-type-parameter type..
//    // dsw: If this is turned back on, be sure to catch the possible
//    // XReprSize exception and add its message to the env.error-s
//    size = expr->type->asRval()->reprSize();
//    TRACE("sizeof", "sizeof(" << expr->exprToString() <<
//                    ") is " << size);

  // dsw: the type of a __builtin_constant_p is an int:
  // http://gcc.gnu.org/onlinedocs/gcc-3.2.2/gcc/Other-Builtins.html#Other%20Builtins
  // TODO: is this right?
  return expr->type->isError()?
           expr->type : env.getSimpleType(ST_UNSIGNED_INT);
}


Type *E___builtin_va_arg::itcheck_x(Env &env, Expression *&replacement)
{
  ASTTypeId::Tcheck tc(DF_NONE, DC_E_BUILTIN_VA_ARG);
  expr->tcheck(env, expr);
  atype = atype->tcheck(env, tc);
  return atype->getType();
}

Type *E___builtin_va_arg_pack::itcheck_x(Env &env, Expression *&replacement)
{
  return env.getSimpleType(ST_VOID);
}

Type *E_typeUnary::itcheck_x(Env &env, Expression *&replacement)
{
  ASTTypeId::Tcheck tc(DF_NONE, DC_E_TYPE_FUNCTION);
  atype = atype->tcheck(env, tc);
  return env.getSimpleType(ST_UNSIGNED_INT);
}

Type *E_typeBinary::itcheck_x(Env &env, Expression *&replacement)
{
  ASTTypeId::Tcheck tc(DF_NONE, DC_E_TYPE_FUNCTION);
  atype0 = atype0->tcheck(env, tc);
  atype1 = atype1->tcheck(env, tc);
  return env.getSimpleType(ST_UNSIGNED_INT);
}


Type *E_alignofType::itcheck_x(Env &env, Expression *&replacement)
{
  ASTTypeId::Tcheck tc(DF_NONE, DC_E_ALIGNOFTYPE);
  atype = atype->tcheck(env, tc);
  Type *t = atype->getType();

  // just assume that the type's size is its alignment; this may
  // be a little conservative for 'double', and will be wrong for
  // large structs, but at the moment it does not seem worthwhile
  // to delve into the details of accurately computing this
  return env.sizeofType(t, alignment, NULL /*expr*/);
}


Type *E_alignofExpr::itcheck_x(Env &env, Expression *&replacement)
{
  expr->tcheck(env, expr);

  // as above, assume size=alignment
  return env.sizeofType(expr->type, alignment, expr);
}


Type *E_statement::itcheck_x(Env &env, Expression *&replacement)
{
  // An E_statement can contain declarations, and tchecking a
  // declaration modifies the environment.  But expressions can occur
  // in ambiguous contexts, and hence their tcheck should not modify
  // the environment.
  //
  // Since the E_statements are themselves interpreted independently
  // of such contexts, tcheck each E_statement exactly once.  Each
  // ambiguous alternative will use the same interpretation.
  //
  // This avoids problems with e.g. in/gnu/c0001.c
  if (!tchecked) {

    // having committed to tchecking here, isolate these actions
    // from the context
    InstantiationContextIsolator isolate(env, env.loc());

    s = s->tcheck(env)->asS_compound();

    tchecked = true;
  }

  if (s->stmts.isNotEmpty()) {
    Statement *last = s->stmts.last();
    if (last->isS_expr()) {
      return last->asS_expr()->expr->getType();
    }
  }

  return env.getSimpleType(ST_VOID, CV_NONE);
}


Type *E_gnuCond::itcheck_x(Env &env, Expression *&replacement)
{
  cond->tcheck(env, cond);
  el->tcheck(env, el);

  // presumably the correct result type is some sort of intersection
  // of the 'cond' and 'el' types?

  return el->type;
}


Type *E_addrOfLabel::itcheck_x(Env &env, Expression *&replacement)
{
  // TODO: check that the label exists in the function
  
  // type is void*
  return env.makePtrType(env.getSimpleType(ST_VOID));
}


// decompose a real/imaginary/complex type:
//   prec: 0=float, 1=double, 2=longdouble
//   axis: 0=real, 1=imag, 2=complex
// return false if not among the nine floating types
bool dissectFloatingType(int &prec, int &axis, Type *t)
{
  t = t->asRval();

  if (!t->isSimpleType()) {
    return false;
  }
  SimpleTypeId id = t->asSimpleTypeC()->type;

  switch (id) {
    case ST_FLOAT:                  prec=0; axis=0; return true;
    case ST_DOUBLE:                 prec=1; axis=0; return true;
    case ST_LONG_DOUBLE:            prec=2; axis=0; return true;

    case ST_FLOAT_IMAGINARY:        prec=0; axis=1; return true;
    case ST_DOUBLE_IMAGINARY:       prec=1; axis=1; return true;
    case ST_LONG_DOUBLE_IMAGINARY:  prec=2; axis=1; return true;

    case ST_FLOAT_COMPLEX:          prec=0; axis=2; return true;
    case ST_DOUBLE_COMPLEX:         prec=1; axis=2; return true;
    case ST_LONG_DOUBLE_COMPLEX:    prec=2; axis=2; return true;

    default: return false;
  }
}

SimpleTypeId constructFloatingType(int prec, int axis)
{
  static SimpleTypeId const map[3/*axis*/][3/*prec*/] = {
    { ST_FLOAT, ST_DOUBLE, ST_LONG_DOUBLE },
    { ST_FLOAT_IMAGINARY, ST_DOUBLE_IMAGINARY, ST_LONG_DOUBLE_IMAGINARY },
    { ST_FLOAT_COMPLEX, ST_DOUBLE_COMPLEX, ST_LONG_DOUBLE_COMPLEX }
  };

  xassert((unsigned)axis < 3);
  xassert((unsigned)prec < 3);

  return map[axis][prec];
}


Type *E_fieldAcc::itcheck_complex_selector(Env &env, LookupFlags flags,
                                           LookupSet &candidates)
{
  int isImag = fieldName->getName()[2] == 'i';

  int prec, axis;
  if (!dissectFloatingType(prec, axis, obj->type) ||
      axis != 2/*complex*/) {
    return env.error(stringc << "can only apply " << fieldName->getName()
                             << " to complex types, not `"
                             << obj->type->toString() << "'");
  }

  field = env.complexComponentFields[isImag][prec];
  return env.tfac.makeReferenceType(field->type);
}


Type *E_binary::itcheck_complex_arith(Env &env)
{
  int prec1, axis1;
  int prec2, axis2;
  if (!dissectFloatingType(prec1, axis1, e1->type) ||
      !dissectFloatingType(prec2, axis2, e2->type)) {
    return env.error(stringc << "invalid complex arithmetic operand types `"
                             << e1->type->toString() << "' and `"
                             << e2->type->toString() << "'");
  }

  // NOTE: The following computations have not been thoroughly tested.

  // result precision: promote to larger
  int prec = max(prec1, prec2);

  // result axis
  int axis;
  switch (op) {
    case BIN_PLUS:
    case BIN_MINUS:
      if (axis1 == axis2) {
        axis = axis1;
      }
      else {
        axis = 2/*complex*/;
      }
      break;

    case BIN_MULT:
    case BIN_DIV:
      if (axis1 + axis2 == 0) {
        axis = 0/*real*/;     // but then how'd we reach this code anyway?
      }
      else if (axis1 + axis2 == 1) {
        axis = 1/*imag*/;
      }
      else {
        axis = 2/*complex*/;
      }
      break;

    default:
      // who the heck knows
      axis = 2/*complex*/;
      break;
  }
  
  // result id
  return env.getSimpleType(constructFloatingType(prec, axis));
}


static void compile_time_compute_int_expr(Env &env, Expression *&e, int &x, char *error_msg) {
  e->tcheck(env, e);
  if (!e->constEval(env, x)) env.error(error_msg);
}

static void check_designator_list(Env &env, FakeList<Designator> *dl)
{
  xassert(dl);
  FAKELIST_FOREACH_NC(Designator, dl, d) {
    if (SubscriptDesignator *sd = dynamic_cast<SubscriptDesignator*>(d)) {
      compile_time_compute_int_expr(env, sd->idx_expr, sd->idx_computed,
                                    "compile-time computation of range start designator array index fails");
      if (sd->idx_expr2) {
        compile_time_compute_int_expr(env, sd->idx_expr2, sd->idx_computed2,
                                      "compile-time computation of range end designator array index fails");
      }
    }
    // nothing to do for FieldDesignator-s
  }
}

void IN_designated::tcheck(Env &env, Type *type)
{
  init->tcheck(env, type);
  check_designator_list(env, designator_list);
}


// ------------------ const-eval, etc. -------------------
CValue E_alignofType::extConstEval(ConstEval &env) const
{
  CValue ret;
  ret.setUnsigned(ST_UNSIGNED_INT, alignment);
  return ret;
}


CValue E_alignofExpr::extConstEval(ConstEval &env) const
{
  CValue ret;
  ret.setUnsigned(ST_UNSIGNED_INT, alignment);
  return ret;
}


CValue E_gnuCond::extConstEval(ConstEval &env) const
{
  CValue v = cond->constEval(env);
  if (v.isSticky()) {
    return v;
  }

  if (!v.isZero()) {
    return v;
  }
  else {
    return el->constEval(env);
  }
}

bool E_gnuCond::extHasUnparenthesizedGT()
{
  return hasUnparenthesizedGT(cond) ||
         hasUnparenthesizedGT(el);
}


// ------------------------ print --------------------------
void TS_typeof::print(PrintEnv &env)
{
  xassert(0);                   // I'll bet this is never called.
//    TreeWalkDebug treeDebug("TS_typeof_expr");
}


void ASTTypeof::printAmbiguities(ostream &os, int indent) const
{
  genericPrintAmbiguities(this, "TypeSpecifier", os, indent);
    
  // sm: what was this here for?
  //genericCheckNexts(this);
}


void ASTTypeof::addAmbiguity(ASTTypeof *alt)
{
  //genericAddAmbiguity(this, alt);
  
  // insert 'alt' at the head of the 'ambiguity' list
  xassert(alt->ambiguity == NULL);
  alt->ambiguity = ambiguity;
  ambiguity = alt;
}


void S_function::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("S_function::iprint");
  f->print(env);
}


void S_rangeCase::iprint(PrintEnv &env)
{                    
  TreeWalkDebug treeDebug("S_rangeCase::iprint");
  *env.out << "case";
  exprLo->print(env);
  *env.out << "...";
  exprHi->print(env);
  *env.out << ":";
  s->print(env);
}


void S_computedGoto::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("S_computedGoto::iprint");
  *env.out << "goto *";
  target->print(env);
  *env.out << ";\n";
}


void E_compoundLit::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E_compoundLit::iprint");
  {
    PairDelim pair(*env.out, "", "(", ")");
    stype->print(env);
  }
  init->print(env);
}

void E___builtin_constant_p::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E___builtin_constant_p::iprint");
  PairDelim pair(*env.out, "__builtin_constant_p", "(", ")");
  expr->print(env);
}

void E___builtin_va_arg::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E___builtin_va_arg::iprint");
  PairDelim pair(*env.out, "__builtin_va_arg", "(", ")");
  expr->print(env);
  *env.out << ", ";
  atype->print(env);
}

void E___builtin_va_arg_pack::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E___builtin_va_arg_pack::iprint");
  PairDelim pair(*env.out, "__builtin_Va_arg_pack", "(", ")");
}

void E_typeUnary::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E_typeUnary::iprint");
  PairDelim pair(*env.out, property, "(", ")");
  atype->print(env);
}

void E_typeBinary::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E_typeBinary::iprint");
  PairDelim pair(*env.out, property, "(", ")");
  atype0->print(env);
  *env.out << ", ";
  atype1->print(env);
}

void E_alignofType::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E_alignofType::iprint");
  PairDelim pair(*env.out, "__alignof__", "(", ")");
  atype->print(env);
}

void E_alignofExpr::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E_alignofType::iprint");
  PairDelim pair(*env.out, "__alignof__", "(", ")");
  expr->print(env);
}

void E_statement::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E_statement::iprint");
  PairDelim pair(*env.out, "", "(", ")");
  s->iprint(env);
}

void E_gnuCond::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E_gnuCond::iprint");
  PairDelim pair(*env.out, "", "(", ")");
  cond->print(env);
  *env.out << " ?: ";
  el->print(env);
}

void E_addrOfLabel::iprint(PrintEnv &env)
{
  TreeWalkDebug treeDebug("E_addrOfLabel::iprint");
  *env.out << "&&" << labelName;
}


// prints designators in the new C99 style, not the obsolescent ":"
// style
static void print_DesignatorList(PrintEnv &env, FakeList<Designator> *dl) {
  xassert(dl);
  FAKELIST_FOREACH_NC(Designator, dl, d) {
    d->print(env);
  }
  *env.out << "=";
}

void IN_designated::print(PrintEnv &env)
{
  print_DesignatorList(env, designator_list);
  init->print(env);
}

// -------------------- Designator ---------------

void FieldDesignator::print(PrintEnv &env)
{
  TreeWalkDebug treeDebug("FieldDesignator");
  xassert(id);
  *env.out << "." << id;
}

void SubscriptDesignator::print(PrintEnv &env)
{
  TreeWalkDebug treeDebug("SubscriptDesignator");
  xassert(idx_expr);
  PairDelim pair(*env.out, "", "[", "]");
  idx_expr->print(env);
  if (idx_expr2) {
    *env.out << " ... ";
    idx_expr2->print(env);
  }
}


void Designator::printAmbiguities(ostream &os, int indent) const
{
  genericPrintAmbiguities(this, "Designator", os, indent);
  
  genericCheckNexts(this);
}

void Designator::addAmbiguity(Designator *alt)
{
  genericAddAmbiguity(this, alt);
}

void Designator::setNext(Designator *newNext)
{
  genericSetNext(this, newNext);
}


// ------------------------ cfg --------------------------

// WARNING: The control flow graph will show that the statement before
// the S_function flows into the S_function and that the S_function
// flows into the next statement.  If you know that an S_function is
// just a function definition and does nothing at run time, this is
// harmless, but it is a little odd, as in reality control would jump
// over the S_function.  The only way to prevent this that I can see
// would be for cfg.cc:Statement::computeCFG() to know about
// S_function which would eliminate the usefulness of having it in the
// gnu extension, or for S_function::icfg to go up and do some surgery
// on edges that have already been added, which I consider to be too
// weird.
//
// Scott says: "the entire S_function::icfg can be empty, just like
// S_skip."
void S_function::icfg(CFGEnv &env) {}

void S_rangeCase::icfg(CFGEnv &env)
{
  env.connectEnclosingSwitch(this, "'case'");
  s->computeCFG(env);
}


void S_computedGoto::icfg(CFGEnv &env)
{
  // The CFG mechanism is not really prepared to deal with computed
  // gotos, so I will do nothing here (so, the CFG will look like
  // control simply flows to the next statement).  It will fall to the
  // client to realize that this is a computed goto, and try to do
  // something appropriate.
}


// ---------------------- D_attribute -------------------------
D_attribute::D_attribute(SourceLoc loc, IDeclarator *base,
                         AttributeSpecifierList *alist_)
  : D_grouping(loc, base),
    alist(alist_)
{}

D_attribute::~D_attribute()
{
  delete alist;
}


void D_attribute::debugPrint(ostream &os, int indent, char const *subtreeName) const
{
  // I don't call D_grouping::debugPrint because I want the
  // output to say "D_attribute", not "D_grouping".

  PRINT_HEADER(subtreeName, D_attribute);

  IDeclarator::debugPrint(os, indent, subtreeName);

  PRINT_SUBTREE(base);
  PRINT_SUBTREE(alist);
}


void D_attribute::traverse(ASTVisitor &vis)
{
  // I chose to override this method purely so that I would be able to
  // put a breakpoint in it if desired, and to have a place to
  // document this intention: its behavior is intended to remain
  // identical to D_grouping.  Don't change it without asking me first.
  D_grouping::traverse(vis);
}


D_attribute *D_attribute::clone() const
{
  D_attribute *ret = new D_attribute(
    loc,
    base? base->clone() : NULL,
    alist? alist->clone() : NULL
  );
  return ret;
}


class AttributeDisambiguator : public ASTVisitorEx {
public:
  virtual void foundAmbiguous(void *obj, void **ambig, char const *kind);
};

void AttributeDisambiguator::foundAmbiguous(void *obj, void **ambig, char const *kind)
{
  // I have virtually no basis for doing actual disambiguation of
  // __attribute__ arguments, and no expectation that I will need any.
  // I will just arbitrarily throw away all of the alternatives beyond
  // the first.
  *ambig = NULL;
}


void D_attribute::tcheck(Env &env, Declarator::Tcheck &dt)
{
  D_grouping::tcheck(env, dt);

  // "disambiguate" the attribute list
  AttributeDisambiguator dis;
  alist->traverse(dis);

  // if the type is not a simple type, don't even consider
  // the __mode__ possibility, since I do not know what it
  // would mean in that case
  if (dt.type->isSimpleType()) {
    // get details about current type
    SimpleTypeId existingId = dt.type->asSimpleTypeC()->type;
    CVFlags existingCV = dt.type->getCVFlags();
    bool uns = isExplicitlyUnsigned(existingId);

    // check for a __mode__ attribute
    SimpleTypeId id = ST_ERROR;    // means no mode was found yet
    for (AttributeSpecifierList *l = alist; l; l = l->next) {
      for (AttributeSpecifier *s = l->spec; s; s = s->next) {
        if (s->attr->isAT_func()) {
          AT_func *f = s->attr->asAT_func();
          if (0==strcmp(f->f, "__mode__") && f->args) {
            Expression *e = f->args->first()->expr;
            if (e->isE_variable()) {
              StringRef mode = e->asE_variable()->name->getName();
              if (0==strcmp(mode, "__QI__")) {
                id = uns? ST_UNSIGNED_CHAR : ST_SIGNED_CHAR;
              }
              else if (0==strcmp(mode, "__HI__")) {
                id = uns? ST_UNSIGNED_SHORT_INT : ST_SHORT_INT;
              }
              else if (0==strcmp(mode, "__SI__")) {
                id = uns? ST_UNSIGNED_INT : ST_INT;
              }
              else if (0==strcmp(mode, "__DI__")) {
                id = uns? ST_UNSIGNED_LONG_LONG : ST_LONG_LONG;
              }
            }
          }
        }
      }
    }

    // change the type according to the mode (if any)
    if (id != ST_ERROR) {
      dt.type = env.getSimpleType(id, existingCV);
    }
  }
}


// EOF
