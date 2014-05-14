/* cipart.lex */
/* interval partition generator for C/C++ */


/* ------------ C prelude ------------ */
%{
#include "array.h"       // ArrayStack
#include "str.h"         // stringc

// this works around a problem with cygwin & fileno
#define YY_NEVER_INTERACTIVE 1

// current file offset
int loc = 0;

// current line number
int lineNum = 1;

// current line start
int lineStart = 0;

// last intraline boundary; -1 for none
int boundary = -1;

// stack of open braces
ArrayStack<int> openBraces;

// stack of lines starts where open braces occur
ArrayStack<int> openBraceLines;

// stack of open paren/brackets
ArrayStack<int> openParens;

// line-starts of open-braces that are now closed and so should
// get a partition at the next end-of-line
ArrayStack<int> pendingBracePair;
                                
// saved values of 'boundary' from outer levels of parentheses
ArrayStack<int> savedBoundaries;

// emit a partition
void emit(int lo, int hi, char const *why);

// handle a comment
void comment();

// handle a string literal
void stringLit();

// update location, moving past yytext
void updLoc();

// close any open intraline boundaries
void finishBoundaries();
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


/* -------------- regexp defns ----------- */
/* horizontal whitespace */
WS          [ \t\f\v\r]

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

/* backslash */
BACKSL        "\\"

/* newline */
NL            "\n"

/* any of 256 source characters */
ANY           ({NOTNL}|{NL})

/* end of line */
EOL           {NL}

/* anything but newline */
NOTNL         .


/* -------------- token rules ------------ */
%%

  /* newline: boundary unless inside parens */
  /* this approximates the old 'delta' behavior of acting at line granularity */
"\n" {
  updLoc();
  if (openParens.isEmpty()) {
    finishBoundaries();
    emit(lineStart, loc-1, (stringc << "line " << lineNum).c_str());
    lineStart = loc;

    while (pendingBracePair.isNotEmpty()) {
      emit(pendingBracePair.pop(), loc-1, "brace pair");
    }
  }
  lineNum++;
}

  /* braces: partition at start/end of containing lines */
"{" {
  finishBoundaries();
  if (pendingBracePair.isNotEmpty()) {
    // just let this open-brace cancel one of the close-braces
    // on the same line 
    int prev = pendingBracePair.pop();
    openBraceLines.push(prev);
    openBraces.push(prev /*approximate; will be fine*/);
  }
  else {
    openBraceLines.push(lineStart);
    openBraces.push(loc);
  }
  updLoc();
}

"}" {
  finishBoundaries();

  // where was the corresponding open-brace?
  int openLineStart = openBraceLines.pop();
  int openChar = openBraces.pop();

  if (openLineStart != lineStart) {
    // this is closing a brace pair started on another line, so
    // schedule an emission when we reach the end of this line
    pendingBracePair.push(openLineStart);
  }
  else {
    // this pair was entirely within one line, so emit it as-is
    emit(openChar, loc, "intraline brace pair");
  }

  updLoc();
}

  /* parens: partition just inside, and save boundary info */
"("|"[" {
  openParens.push(loc+1);      // just inside
  savedBoundaries.push(boundary);
  boundary = -1;
  updLoc();
}

"]"|")" {
  int openLoc = openParens.pop();

  finishBoundaries();

  // bound the contents inside the parens
  emit(openLoc, loc-1, "contents of parens");

  // restore old boundary info
  boundary = savedBoundaries.pop();
  updLoc();
}


  /* punctuation, operators: intraline boundary */
"->"               |
"::"               |
"."                |
"!"                |
"~"                |
"+"                |
"-"                |
"++"               |
"--"               |
"&"                |
"*"                |
".*"               |
"->*"              |
"/"                |
"%"                |
"<<"               |
">>"               |
"<"                |
"<="               |
">"                |
">="               |
"=="               |
"!="               |
"^"                |
"|"                |
"&&"               |
"||"               |
"?"                |
":"                |
"="                |
"*="               |
"/="               |
"%="               |
"+="               |
"-="               |
"&="               |
"^="               |
"|="               |
"<<="              |
">>="              |
","                |
"..."              |
"<%"               |
"%>"               |
"<:"               |
":>"               |
"and"              |
"bitor"            |
"or"               |
"xor"              |
"compl"            |
"bitand"           |
"and_eq"           |
"or_eq"            |
"xor_eq"           |
"not"              |
"not_eq"           |
".."               {
  finishBoundaries();

  // open a new boundary on the operator
  boundary = loc;

  updLoc();
}


  /* semicolon: close open boundaries, but don't start any
   * (sort of line newline) */
";" {
  finishBoundaries();

  updLoc();
}


  /* C++ comment */
{WS}*"//".*    {
  comment();
}

  /* C comment */
"/""*"([^*]|"*"*[^*/])*"*"+"/"     {
  comment();
}

  /* unterminated C comment */
"/""*"([^*]|"*"*[^*/])*"*"*        {
  comment();
}


  /* string literal */
"L"?{QUOTE}({STRCHAR}|{ESCAPE})*{QUOTE} {
  stringLit();
}

  /* string literal missing final quote */
"L"?{QUOTE}({STRCHAR}|{ESCAPE})*{EOL}   {
  stringLit();
}

  /* unterminated string literal at EOF */
"L"?{QUOTE}({STRCHAR}|{ESCAPE})*{BACKSL}? {
  stringLit();
}


  /* character literal */
"L"?{TICK}({CCCHAR}|{ESCAPE})*{TICK}   {
  stringLit();
}

  /* character literal missing final tick */
"L"?{TICK}({CCCHAR}|{ESCAPE})*{EOL}    {
  stringLit();
}

  /* unterminated character literal */
"L"?{TICK}({CCCHAR}|{ESCAPE})*{BACKSL}?  {
  stringLit();
}


  /* anything else: ignore */
.  {
  updLoc();
}

<<EOF>> {
  yyterminate();
}


%%
/* ----------------- C epilogue --------------- */

#include "exc.h"         // xbase
#include "autofile.h"    // AutoFILE

// output file
FILE *out;

void emit(int lo, int hi, char const *why)
{
  if (lo <= hi) {
    fprintf(out, "%d,%d; \t// %s\n", lo, hi, why);
  }
  else {
    // happens for example when we have empty parens and try
    // to identify their contents; just drop it
  }
}


void comment()
{
  emit(loc, loc+yyleng-1, "comment");
  updLoc();
}


// for string literals, regard all the text as optional except
// the first character
void stringLit()
{
  char *begin = yytext;
  if (*begin == 'L') {
    begin++;
  }
  begin++;                        // now 'begin' points to first non-quote char
  begin++;                        // second non-quote char

  char *end = yytext-yyleng-2;    // 'end' points to last non-quote char

  if (end >= begin) {
    // mark the chars between begin and end, inclusive
    emit(loc + (begin-yytext), loc + (end-yytext), "string lit contents - 1");
  }
  
  updLoc();
}


void updLoc()
{
  loc += yyleng;
}


void finishBoundaries()
{
  if (boundary != -1) {
    // finish the intraline boundary
    emit(boundary, loc-1, "intraline boundary");
    boundary = -1;
  }
}


void entry(int argc, char *argv[])
{
  xBase::logExceptions = false;

  if (argc != 2) {
    xbase(stringc << "usage: " << argv[0] << " foo.c\n"
                  << "  writes foo.c.str");
  }

  string fname = argv[1];
  AutoFILE fp(toCStr(fname), "r");
  yyrestart(fp);

  string outfname = stringc << fname << ".str";
  AutoFILE outfp(toCStr(outfname), "w");
  out = outfp;

  fprintf(out, "// %s\n", outfname.c_str());
  fprintf(out, "// generated automatically by %s from %s\n\n",
               argv[0], fname.c_str());

  try {
    yylex();
  }
  catch (xBase &x) {
    x.addContext(stringc << "lexing on line " << lineNum);
    throw;
  }
}


int main(int argc, char *argv[])
{
  try {
    entry(argc, argv);
    return 0;
  }
  catch (xBase &x) {
    cout << x.why() << endl;
    return 4;
  }
}


  /* EOF */
