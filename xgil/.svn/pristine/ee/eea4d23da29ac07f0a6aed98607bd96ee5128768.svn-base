/* iptparse.lex */
/* lexer for iptree parser */


/* ------------ C prelude ------------ */
%{
#include "iptparse.h"       // token definitions
#include "exc.h"            // xfatal

// this works around a problem with cygwin & fileno
#define YY_NEVER_INTERACTIVE 1

int lexerSval = 0;
%}


/* ------------ flex options ----------- */
/* no wrapping is needed; setting this means we don't have to link with libfl.a */
%option noyywrap

/* don't use the default-echo rules */
%option nodefault

/* I don't call unput */
%option nounput

/* the scanner is never interactive */
%option never-interactive


/* -------------- token rules ------------ */
%%

  /* punctuation */
","              { return TOK_COMMA; }
";"              { return TOK_SEMICOLON; }

  /* decimal integer literal */
[0-9]+ {
  lexerSval = atoi(yytext);
  return TOK_INTLIT;
}

  /* whitespace; ignore */
[ \t\n\f\v\r]+  {
}

  /* C++ comment */
"//".*    {
}

.  {
  xfatal("illegal character: `" << yytext[0] << "'");
}

<<EOF>> {
  yyterminate();
}


%%
/* ----------------- C epilogue --------------- */

TokenType getNextToken()
{
  int code = yylex();
  xassert(0 <= code && code < NUM_TOKENTYPES);
  return (TokenType)code;
}

  /* EOF */
