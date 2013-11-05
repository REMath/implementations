/* astxml_lexer0_top.lex            see license.txt for copyright and terms of use
 * flex description of scanner for C and C++ souce
 */

/* This file is the top part of the generated .lex file. */

/* ----------------------- C definitions ---------------------- */
%{

#include "astxml_lexer.h"       // Lexer class

// this works around a problem with cygwin & fileno
#define YY_NEVER_INTERACTIVE 1

%}


/* -------------------- flex options ------------------ */
/* no wrapping is needed; setting this means we don't have to link with libfl.a */
%option noyywrap

/* don't use the default-echo rules */
%option nodefault

/* I don't call unput */
%option nounput

/* generate a c++ lexer */
%option c++

/* use the "fast" algorithm with no table compression */
%option full

/* utilize character equivalence classes */
%option ecs

/* the scanner is never interactive */
%option never-interactive

/* I want to give good error messages and flex is way faster than a
   parser so I think this is a good tradeoff; UPDATE: arg, Scott's
   scheme seems to require %option full just to work at all and which
   seems to contradict this option. */
  /* %option yylineno */

/* and I will define the class (lexer.h) */
%option yyclass="AstXmlLexer"

/* ------------------- definitions -------------------- */
/* newline */
NL            "\n"

/* anything but newline */
NOTNL         .

/* any of 256 source characters */
ANY           ({NOTNL}|{NL})

/* backslash */
BACKSL        "\\"

/* beginnging of line (must be start of a pattern) */
BOL           ^

/* end of line (would like EOF to qualify also, but flex doesn't allow it */
EOL           {NL}

/* letter or underscore */
LETTER        [A-Za-z_]
LETTERDOT     [A-Za-z_\.]

/* letter or underscore or digit */
ALNUM         [A-Za-z_0-9]
ALNUMDOT      [A-Za-z_0-9\.]

/* decimal digit */
DIGIT         [0-9]
HEXDIGIT      [0-9A-Fa-f]

/* sequence of decimal digits */
DIGITS        ({DIGIT}+)
/* sequence of hex digits */
HEXDIGITS     ({HEXDIGIT}+)

/* sign of a number */
SIGN          ("+"|"-")

/* integer suffix */
/* added 'LL' option for gcc/c99 long long compatibility */
ELL_SUFFIX    [lL]([lL]?)
INT_SUFFIX    ([uU]{ELL_SUFFIX}?|{ELL_SUFFIX}[uU]?)

/* floating-point suffix letter */
FLOAT_SUFFIX  [flFL]

/* normal string character: any but quote, newline, or backslash */
STRCHAR       [^\"\n\\]

/* (start of) an escape sequence */
ESCAPE        ({BACKSL}{ANY})

/* double quote */
QUOTE         [\"]

/* normal character literal character: any but single-quote, newline, or backslash */
CCCHAR        [^\'\n\\]

/* single quote */
TICK          [\']

/* space or tab */
SPTAB         [ \t]

/* preprocessor "character" -- any but escaped newline */
PPCHAR        ([^\\\n]|{BACKSL}{NOTNL})


/* ------------- token definition rules --------------- */
%%

  /* operators, punctuators and keywords: tokens with one spelling */
"<"                return tok(XTOK_LESSTHAN);
">"                return tok(XTOK_GREATERTHAN);
"/"                return tok(XTOK_SLASH);
"="                return tok(XTOK_EQUAL);
