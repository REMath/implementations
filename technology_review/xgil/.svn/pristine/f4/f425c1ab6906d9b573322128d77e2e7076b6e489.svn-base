  /* gnu.lex
   * extension to cc.lex, for GNU extensions
   */

"__builtin_constant_p" return tok(TOK_BUILTIN_CONSTANT_P);
"__alignof"            return tok(TOK___ALIGNOF__);
"__alignof__"          return tok(TOK___ALIGNOF__);

"__attribute"          return tok(TOK___ATTRIBUTE__);
"__attribute__"        return tok(TOK___ATTRIBUTE__);
"__label__"            return tok(TOK___LABEL__);
"typeof"               return tok(TOK___TYPEOF__);
"__typeof"             return tok(TOK___TYPEOF__);
"__typeof__"           return tok(TOK___TYPEOF__);
"__builtin_expect"     return tok(TOK___BUILTIN_EXPECT);
"__builtin_offsetof"   return tok(TOK___BUILTIN_OFFSETOF);

"__builtin_va_arg"       return tok(TOK___BUILTIN_VA_ARG);
"__builtin_va_arg_pack"  return tok(TOK___BUILTIN_VA_PACK);

"__null" {
  // gcc only recognizes __null as 0 in C++ mode, but I prefer the
  // simplicity of always doing it; This is Scott's inlined and
  // modified Lexer::svalTok()
  checkForNonsep(TOK_INT_LITERAL);
  updLoc();
  sval = (SemanticValue)addString("0", 1);
  return TOK_INT_LITERAL;
}

  /* behavior of these depends on CCLang settings */
"__FUNCTION__"|"__PRETTY_FUNCTION__" {
  if (lang.gccFuncBehavior == CCLang::GFB_string) {
    // yield with special token codes
    return tok(yytext[2]=='F'? TOK___FUNCTION__ : TOK___PRETTY_FUNCTION__);
  }
  else {
    // ordinary identifier, possibly predefined (but that's not the
    // lexer's concern)
    return svalTok(TOK_NAME);
  }
}

  /* hex floating literal: This is actually a C99-ism.
     See http://gcc.gnu.org/onlinedocs/gcc-3.4.1/gcc/Hex-Floats.html
     and C99 6.4.4.2.
  */
[0][xX]{HEXDIGITS}"."{HEXDIGITS}?[pP]{SIGN}?{DIGITS}{FLOAT_SUFFIX}?   |
[0][xX]{HEXDIGITS}"."?[pP]{SIGN}?{DIGITS}{FLOAT_SUFFIX}?              |
[0][xX]"."{HEXDIGITS}[pP]{SIGN}?{DIGITS}{FLOAT_SUFFIX}?               {
  return svalTok(TOK_FLOAT_LITERAL);
}

  /* malformed hex literal: missing 'p' */
[0][xX]{HEXDIGITS}"."{HEXDIGITS}?     |
[0][xX]"."{HEXDIGITS}?                {
  err("hex literal missing 'p'");
  return svalTok(TOK_FLOAT_LITERAL);
}

  /* malformed hex literal: no digits after 'p' */
[0][xX]{HEXDIGITS}"."{HEXDIGITS}?[pP]{SIGN}?       |
[0][xX]{HEXDIGITS}"."?[pP]{SIGN}?                  |
[0][xX]"."{HEXDIGITS}[pP]{SIGN}?                   {
  err("hex literal must have digits after 'p'");
  return svalTok(TOK_FLOAT_LITERAL);
}


"__extension__" {
  /* treat this like a token, in that nonseparating checks are done,
   * but don't yield it to the parser */
  (void)tok(TOK___EXTENSION__);
}

  /* GNU alternate spellings; the versions with both leading and trailling
     underscores are explained here:
       http://gcc.gnu.org/onlinedocs/gcc-3.1/gcc/Alternate-Keywords.html
     But, I see no explanation for the ones with only leading underscores,
     though they occur in code in the wild so we support them...
   */
"__asm"                return tok(TOK_ASM);
"__asm__"              return tok(TOK_ASM);
"__const"              return tok(TOK_CONST);
"__const__"            return tok(TOK_CONST);
"__restrict"           return tok(TOK_RESTRICT);
"__restrict__"         return tok(TOK_RESTRICT);
"__inline"             return tok(TOK_INLINE);
"__inline__"           return tok(TOK_INLINE);
"__signed"             return tok(TOK_SIGNED);
"__signed__"           return tok(TOK_SIGNED);
"__volatile"           return tok(TOK_VOLATILE);
"__volatile__"         return tok(TOK_VOLATILE);
"__complex__"          return tok(TOK_COMPLEX);
"__imaginary__"        return tok(TOK_IMAGINARY);
"__real__"             return tok(TOK_REAL);
"__imag__"             return tok(TOK_IMAG);
"__thread"             return tok(TOK_THREAD);

"<?"                   return tok(TOK_MIN_OP);
">?"                   return tok(TOK_MAX_OP);

  /* bhackett: functions on types from http://msdn.microsoft.com/en-us/library/ms177194.aspx,
     this is also used in GNU code.
  */
"__has_assign"                  return svalTok(TOK_TYPE_UNARY);
"__has_copy"                    return svalTok(TOK_TYPE_UNARY);
"__has_finalizer"               return svalTok(TOK_TYPE_UNARY);
"__has_nothrow_assign"          return svalTok(TOK_TYPE_UNARY);
"__has_nothrow_constructor"     return svalTok(TOK_TYPE_UNARY);
"__has_nothrow_copy"            return svalTok(TOK_TYPE_UNARY);
"__has_trivial_assign"          return svalTok(TOK_TYPE_UNARY);
"__has_trivial_constructor"     return svalTok(TOK_TYPE_UNARY);
"__has_trivial_copy"            return svalTok(TOK_TYPE_UNARY);
"__has_trivial_destructor"      return svalTok(TOK_TYPE_UNARY);
"__has_user_destructor"         return svalTok(TOK_TYPE_UNARY);
"__has_virtual_destructor"      return svalTok(TOK_TYPE_UNARY);
"__is_abstract"                 return svalTok(TOK_TYPE_UNARY);
"__is_class"                    return svalTok(TOK_TYPE_UNARY);
"__is_delegate"                 return svalTok(TOK_TYPE_UNARY);
"__is_empty"                    return svalTok(TOK_TYPE_UNARY);
"__is_enum"                     return svalTok(TOK_TYPE_UNARY);
"__is_interface_class"          return svalTok(TOK_TYPE_UNARY);
"__is_pod"                      return svalTok(TOK_TYPE_UNARY);
"__is_polymorphic"              return svalTok(TOK_TYPE_UNARY);
"__is_ref_array"                return svalTok(TOK_TYPE_UNARY);
"__is_ref_class"                return svalTok(TOK_TYPE_UNARY);
"__is_sealed"                   return svalTok(TOK_TYPE_UNARY);
"__is_simple_value_class"       return svalTok(TOK_TYPE_UNARY);
"__is_union"                    return svalTok(TOK_TYPE_UNARY);
"__is_value_class"              return svalTok(TOK_TYPE_UNARY);
"__builtin_types_compatible_p"  return svalTok(TOK_TYPE_BINARY);
"__is_base_of"                  return svalTok(TOK_TYPE_BINARY);
"__is_convertible_to"           return svalTok(TOK_TYPE_BINARY);


  /* Identifier with dollar-sign.
   *   http://gcc.gnu.org/onlinedocs/gcc-3.1/gcc/Dollar-Signs.html
   * The rules are written so that at least one "$" must be present,
   * to avoid obviating the rule in cc.lex. */
"$"({ALNUM}|"$")* {
  return svalTok(TOK_NAME);
}
{LETTER}{ALNUM}*"$"({ALNUM}|"$")* {
  return svalTok(TOK_NAME);
}

  /* C99 stuff */
"restrict" {
  if (lang.restrictIsAKeyword) {
    return tok(TOK_RESTRICT);
  }
  else {
    return svalTok(TOK_NAME);
  }
}

"_Complex"             return tok(TOK_COMPLEX);
"_Imaginary"           return tok(TOK_IMAGINARY);

  /* EOF */
