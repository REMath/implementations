/* grammar.lex
 * lexical analyzer for my grammar input format
 *
 * The variety of syntaxes for embedded literal code cause this lexer
 * to have some of the context sensitivity usually associated with a
 * parser.  This context doesn't nest arbitrarily deeply, so the
 * language recognized is still regular, but clearly there's some
 * design tension.
 */

/* ----------------- C definitions -------------------- */
%{

// pull in my declaration of the lexer class -- this defines
// the additional lexer state, some of which is used in the
// action rules below (this is in the ../ast/ directory now)
#include "gramlex.h"

// pull in the bison-generated token codes
#include "grampar.codes.h"

#include <string.h>     // strchr, strrchr

// for maintaining column count
#define TOKEN_START  tokenStartLoc = fileState.loc /* user ; */
#define UPD_COL      \
  fileState.loc = sourceLocManager->advCol(fileState.loc, yyleng)  /* user ; */
#define TOK_UPD_COL  TOKEN_START; UPD_COL  /* user ; */

%}


/* -------------------- flex options ------------------ */
/* no wrapping is needed; setting this means we don't have to link with libfl.a */
%option noyywrap

/* don't use the default-echo rules */
%option nodefault

/* generate a c++ lexer */
%option c++

/* and I will define the class */
%option yyclass="GrammarLexer"


/* ------------------- definitions -------------------- */
/* any character, including newline */
ANY       (.|"\n")

/* any character except newline */
ANYBUTNL  .

/* starting character in a name */
LETTER    [a-zA-Z_]

/* starting character in a numeric literal */
DIGIT     [0-9]

/* double-quote */
DQUOTE    "\""

/* character that can appear in a quoted string */
/* (I currently don't have any backslash codes, but I want to
 * leave open that possibility, so for now backslashes are illegal) */
STRCHR    [^\n\\\"]

/* non-newline whitespace */
HWHITE    [ \t\f\v\r]


/* --------------- start conditions ------------------- */
/* eating a comment delimited by slash-star and star-slash; note
 * that we remember our current state when entering C_COMMENT,
 * and restore it on exit */
%x C_COMMENT

/* looking for the file name in an "include" directive */
%x INCLUDE

/* recovering from an error by skipping to the next newline */
%x EAT_TO_NEWLINE

/* gathering literal embedded code; the delimiter is specified
 * in the 'embedFinish' variable */
%x LITCODE

/* tokenizing the right-hand side of a production; this one is not
 * exclusive because tokenization is virtually the same in RHS
 * mode as in INITIAL mode */
%s RHS

/* tokenizing parameter list of a function, leading into the
 * embedded code that is its body */
%s FUN

/* looking for the start of a type that follows "token" or "nonterm",
 * or the TOK_NAME meaning the type has been omitted */
%s OPTIONAL_TYPE


/* ---------------------- rules ----------------------- */
%%

  /* -------- whitespace ------ */
"\n" {
  newLine();
}

{HWHITE}+ {
  UPD_COL;
}

  /* -------- comments -------- */
"/""*" {
  /* C-style comments */
  TOKEN_START;
  UPD_COL;
  prevState = YY_START;
  BEGIN(C_COMMENT);
}

<C_COMMENT>{
  "*/" {
    /* end of comment */
    UPD_COL;
    BEGIN(prevState);
  }

  . {
    /* anything but slash-star or newline -- eat it */
    UPD_COL;
  }

  "\n" {
    newLine();
  }

  <<EOF>> {
    UPD_COL;      // <<EOF>> yyleng is 1!
    errorUnterminatedComment();
    return TOK_EOF;
  }
}


"//".*"\n" {
  /* C++-style comment -- eat it */
  TOKEN_START;
  advCol(yyleng-1);   // don't count newline
  newLine();          // count it here
}


  /* -------- punctuators, operators, keywords --------- */
"}"                TOK_UPD_COL;  return TOK_RBRACE;
":"                TOK_UPD_COL;  return TOK_COLON;
")"                TOK_UPD_COL;  return TOK_RPAREN;
","                TOK_UPD_COL;  return TOK_COMMA;

"terminals"        TOK_UPD_COL;  return TOK_TERMINALS;
"precedence"       TOK_UPD_COL;  return TOK_PRECEDENCE;
"option"           TOK_UPD_COL;  return TOK_OPTION;
"expect"           TOK_UPD_COL;  return TOK_EXPECT;
"subsets"          TOK_UPD_COL;  return TOK_SUBSETS;
"replace"          TOK_UPD_COL;  return TOK_REPLACE;
"delete"           TOK_UPD_COL;  return TOK_DELETE;
"forbid_next"      TOK_UPD_COL;  return TOK_FORBID_NEXT;
"error"            TOK_UPD_COL;  return TOK_ERROR;


  /* ----------- sequences that begin literal code ------------ */
  /* for the time being, a "[" will always start an embedded sequence;
   * eventually, I'll remove this in favor of the brace- and paren-
   * delimited embedded sequences */
"[" {
  TOK_UPD_COL;
  BEGIN(LITCODE);
  beginEmbed(']', TOK_LIT_CODE);
}

  /* the "->" operator moves us into RHS mode, which is special because
   * in this mode any "{" is interpreted as the beginning of an embedded
   * section of literal code */
"->" {
  TOK_UPD_COL;
  BEGIN(RHS);
  return TOK_ARROW;
}

  /* "{" in a RHS begins embedded */
<RHS,FUN>"{" {
  TOK_UPD_COL;
  BEGIN(LITCODE);
  beginEmbed('}', TOK_LIT_CODE);
}

  /* otherwise it's just a "{" */
<INITIAL>"{" {
  TOK_UPD_COL;
  return TOK_LBRACE;
}

  /* since right-hand-sides can end with either embedded code or a simple
   * ";", the semicolon gets out of RHS mode */
<INITIAL,RHS>";" {
  TOK_UPD_COL;
  BEGIN(INITIAL);     // if in RHS, reset to INITIAL
  return TOK_SEMICOLON;
}

  /* "token" and "nonterm" are always followed by an optional type,
   * and then a TOK_NAME.  So, until we see a TOK_NAME, "(" will mean
   * the start of an embedded sequence. */
"token"|"nonterm" {
  TOK_UPD_COL;
  BEGIN(OPTIONAL_TYPE);
  return yytext[0]=='t'? TOK_TOKEN : TOK_NONTERM;
}

  /* so now this begins embedded */
<OPTIONAL_TYPE>"(" {
  TOK_UPD_COL;
  BEGIN(LITCODE);
  beginEmbed(')', TOK_LIT_CODE);
}

  /* otherwise it's just itself */
<INITIAL,RHS,FUN>"(" {
  TOK_UPD_COL;
  return TOK_LPAREN;
}

  /* function beginning */
"fun" {
  TOK_UPD_COL;
  BEGIN(FUN);            // treat "{" as beginning literal code
  return TOK_FUN;
}

  /* verbatim beginning */
"verbatim"|"impl_verbatim" {
  TOK_UPD_COL;
  BEGIN(FUN);            // close enough
  return yytext[0]=='v'? TOK_VERBATIM : TOK_IMPL_VERBATIM;
}


  /* --------- embedded literal code --------- */
  /* no TOKEN_START here; we'll use the tokenStartLoc that
   * was computed in the opening punctuation */
<LITCODE>{
  [^\]\})\n]+ {
    UPD_COL;
    embedded->handle(yytext, yyleng, embedFinish);
  }

  "\n" {
    newLine();
    embedded->handle(yytext, yyleng, embedFinish);
  }

  ("]"|"}"|")") {
    UPD_COL;
    if (embedded->zeroNesting()) {
      // done
      BEGIN(INITIAL);

      // check for balanced delimiter
      if (embedFinish != yytext[0]) {
        err("unbalanced literal code delimiter");
      }

      // don't add "return" or ";"
      embedded->exprOnly = false;

      // can't extract anything
      embedded->isDeclaration = false;

      // caller can get text from embedded->text
      return embedMode;
    }
    else {
      // delimeter paired within the embedded code, mostly ignore it
      embedded->handle(yytext, yyleng, embedFinish);
    }
  }

  <<EOF>> {
    err(stringc << "hit end of file while looking for final `"
                << embedFinish << "'");
    yyterminate();
  }
}


  /* embedded *type* description */
"context_class" {
  /* caller will get text from yytext and yyleng */
  TOK_UPD_COL;

  /* drop into literal-code processing */
  BEGIN(LITCODE);

  /* I reset the initial nesting to -1 so that the '{' at the
   * beginning of the class body sets nesting to 0, thus when
   * I see the final '}' I'll see that at level 0 and stop */
  beginEmbed('}', TOK_LIT_CODE, -1);

  return TOK_CONTEXT_CLASS;
}


  /* ---------- includes ----------- */
"include" {
  TOK_UPD_COL;    /* hence no TOKEN_START in INCLUDE area */
  BEGIN(INCLUDE);
}

<INCLUDE>{
  {HWHITE}*"("{HWHITE}*{DQUOTE}{STRCHR}+{DQUOTE}{HWHITE}*")" {
    /* e.g.: ("filename") */
    /* file name to include */
    UPD_COL;

    /* find quotes */
    char *leftq = strchr(yytext, '"');
    char *rightq = strchr(leftq+1, '"');
    xassert(leftq && rightq);

    /* extract filename string */
    includeFileName = addString(leftq+1, rightq-leftq-1);

    /* go back to normal processing */
    BEGIN(INITIAL);
    return TOK_INCLUDE;
  }

  {ANY}      {
    /* anything else: malformed */
    UPD_COL;
    errorMalformedInclude();

    /* rudimentary error recovery.. */
    BEGIN(EAT_TO_NEWLINE);
  }
}

<EAT_TO_NEWLINE>{
  .+ {
    UPD_COL;
    /* not newline, eat it */
  }

  "\n" {
    /* get out of here */
    newLine();
    BEGIN(INITIAL);
  }
}

  /* -------- name literal --------- */
{LETTER}({LETTER}|{DIGIT})* {
  /* get text from yytext and yyleng */
  TOK_UPD_COL;
  if (YY_START == OPTIONAL_TYPE) {
    BEGIN(INITIAL);      // bail out of OPTIONAL_TYPE mode
  }
  return TOK_NAME;
}

  /* -------- numeric literal ------ */
{DIGIT}+ {
  TOK_UPD_COL;
  integerLiteral = strtoul(yytext, NULL, 10 /*radix*/);
  return TOK_INTEGER;
}

  /* ----------- string literal ----- */
{DQUOTE}{STRCHR}*{DQUOTE} {
  TOK_UPD_COL;
  stringLiteral = addString(yytext+1, yyleng-2);        // strip quotes
  return TOK_STRING;
}

  /* --------- illegal ------------- */
{ANY} {
  TOK_UPD_COL;
  errorIllegalCharacter(yytext[0]);
}


%%
/* -------------------- additional C code -------------------- */

// identify tokens representing embedded text
bool isGramlexEmbed(int code)
{
  return code == TOK_LIT_CODE;
}
