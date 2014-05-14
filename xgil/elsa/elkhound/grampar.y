/* grammar.y            see license.txt for copyright and terms of use
 * parser for grammar files with new ast format */


/* C declarations */
%{

#include "grampar.h"        // yylex, etc.
#include "gramast.ast.gen.h"// grammar syntax AST definition
#include "gramlex.h"        // GrammarLexer
#include "owner.h"          // Owner

#include <stdlib.h>         // malloc, free

// enable debugging the parser
#ifndef NDEBUG
  #define YYDEBUG 1
#endif

// name of extra parameter to yylex
#define YYLEX_PARAM parseParam

// make it call my yylex
#define yylex(lv, param) grampar_yylex(lv, param)

// Bison calls yyerror(msg) on error; we need the extra
// parameter too, so the macro shoehorns it in there
#define yyerror(msg) grampar_yyerror(msg, YYPARSE_PARAM)

// rename the externally-visible parsing routine to make it
// specific to this instance, so multiple bison-generated
// parsers can coexist
#define yyparse grampar_yyparse


// grab the parameter
#define PARAM ((ParseParams*)parseParam)

// return a locstring for 'str' with no location information
#define noloc(str)                                                    \
  new LocString(SL_UNKNOWN,      /* unknown location */               \
                PARAM->lexer.strtable.add(str))
                
// locstring for NULL, with no location
#define nolocNULL()                                                   \
  new LocString(SL_UNKNOWN, NULL)

// return a locstring with same location info as something else
// (passed as a pointer to a SourceLocation)
#define sameloc(otherLoc, str)                                        \
  new LocString(otherLoc->loc, PARAM->lexer.strtable.add(str))

// interpret the word into an associativity kind specification
AssocKind whichKind(LocString * /*owner*/ kind);

%}


/* ================== bison declarations =================== */
// don't use globals
%pure_parser


/* ===================== tokens ============================ */
/* tokens that have many lexical spellings */
%token <num> TOK_INTEGER
%token <str> TOK_NAME
%token <str> TOK_STRING
%token <str> TOK_LIT_CODE

/* punctuators */
%token TOK_LBRACE "{"
%token TOK_RBRACE "}"
%token TOK_COLON ":"
%token TOK_SEMICOLON ";"
%token <loc> TOK_ARROW "->"
%token TOK_LPAREN "("
%token TOK_RPAREN ")"
%token TOK_COMMA ","

/* keywords */
%token TOK_TERMINALS "terminals"
%token TOK_TOKEN "token"
%token TOK_NONTERM "nonterm"
%token TOK_FUN "fun"
%token TOK_VERBATIM "verbatim"
%token TOK_IMPL_VERBATIM "impl_verbatim"
%token TOK_PRECEDENCE "precedence"
%token TOK_OPTION "option"
%token TOK_EXPECT "expect"
%token TOK_CONTEXT_CLASS "context_class"
%token TOK_SUBSETS "subsets"
%token TOK_DELETE "delete"
%token TOK_REPLACE "replace"
%token TOK_FORBID_NEXT "forbid_next"
%token TOK_ERROR "error"

// left, right, nonassoc: they're not keywords, since "left" and "right"
// are common names for RHS elements; instead, we parse them as names
// and interpret them after lexing


/* ===================== types ============================ */
/* all pointers are owner pointers */
%union {
  int num;
  LocString *str;
  SourceLoc loc;

  ASTList<TopForm> *topFormList;
  TopForm *topForm;

  ASTList<TermDecl> *termDecls;
  TermDecl *termDecl;
  ASTList<TermType> *termTypes;
  TermType *termType;
  ASTList<PrecSpec> *precSpecs;

  ASTList<SpecFunc> *specFuncs;
  SpecFunc *specFunc;
  ASTList<LocString> *stringList;

  ASTList<ProdDecl> *prodDecls;
  ProdDecl *prodDecl;
  ASTList<RHSElt> *rhsList;
  RHSElt *rhsElt;
}

%type <num> StartSymbol
%type <str> Type Action

%type <topFormList> TopFormList
%type <topForm> TopForm ContextClass Verbatim Option Terminals Nonterminal

%type <termDecls> TermDecls
%type <termDecl> TerminalDecl
%type <termTypes> TermTypes
%type <termType> TermType
%type <precSpecs> Precedence PrecSpecs
%type <stringList> NameOrStringList
%type <str> NameOrString

%type <specFuncs> SpecFuncs
%type <specFunc> SpecFunc
%type <stringList> FormalsOpt Formals Subsets

%type <prodDecls> Productions
%type <prodDecl> Production
%type <rhsList> RHS
%type <rhsElt> RHSElt


/* ===================== productions ======================= */
%%

/* The actions in this file simply build an Abstract Syntax Tree (AST)
 * for later processing. */


/* start symbol */
/* yields: int (dummy value) */
StartSymbol: TopFormList     
               { ((ParseParams*)parseParam)->treeTop = new GrammarAST($1); $$=0; }
           ;

/* yields: ASTList<TopForm> */
TopFormList: /*empty*/              { $$ = new ASTList<TopForm>; }
           | TopFormList TopForm    { ($$=$1)->append($2); }
           ;
           
/* yields: TopForm */
TopForm: ContextClass               { $$ = $1; }
       | Verbatim                   { $$ = $1; }
       | Option                     { $$ = $1; }
       | Terminals                  { $$ = $1; }
       | Nonterminal                { $$ = $1; }
       ;

/* yields: TopForm (always TF_context) */
ContextClass: "context_class" TOK_LIT_CODE ";"
                { $$ = new TF_context($2); }
            ;

/* yields: TopForm (always TF_verbatim) */
Verbatim: "verbatim" TOK_LIT_CODE          { $$ = new TF_verbatim(false, $2); }
        | "impl_verbatim" TOK_LIT_CODE     { $$ = new TF_verbatim(true, $2); }
        ;

/* yields: TopForm (always TF_option) */
/* options without specified values default to a value of 1 */
Option: "option" TOK_NAME ";"              { $$ = new TF_option($2, 1); }
      | "option" TOK_NAME TOK_INTEGER ";"  { $$ = new TF_option($2, $3); }
      ;


/* ------ terminals ------ */
/*
 * the terminals are the grammar symbols that appear only on the RHS of
 * forms; they are the output of the lexer; the Terminals list declares
 * all of the terminals that will appear in the rules
 */
/* yields: TopForm (always TF_terminals) */
Terminals: "terminals" "{" TermDecls TermTypes Precedence "}"
             { $$ = new TF_terminals($3, $4, $5); }
         ;

/* yields: ASTList<TermDecl> */
TermDecls: /* empty */                             { $$ = new ASTList<TermDecl>; }
         | TermDecls TerminalDecl                  { ($$=$1)->append($2); }
         ;

/* each terminal has an integer code which is the integer value the
 * lexer uses to represent that terminal.  it is followed by a
 * canonical name, and an optional alias; the name/alias appears in
 * the forms, rather than the integer code itself */
/* yields: TermDecl */
TerminalDecl: TOK_INTEGER ":" TOK_NAME ";"
                { $$ = new TermDecl($1, $3, sameloc($3, "")); }
            | TOK_INTEGER ":" TOK_NAME TOK_STRING ";"
                { $$ = new TermDecl($1, $3, $4); }
            ;

/* yields: LocString */
Type: TOK_LIT_CODE                    { $$ = $1; }
    | /* empty */                     { $$ = nolocNULL(); }
    ;

/* yields: ASTList<TermType> */
TermTypes: /* empty */                { $$ = new ASTList<TermType>; }
         | TermTypes TermType         { ($$=$1)->append($2); }
         ;

/* yields: TermType */
TermType: "token" Type TOK_NAME ";"
            { $$ = new TermType($3, $2, new ASTList<SpecFunc>); }
        | "token" Type TOK_NAME "{" SpecFuncs "}"
            { $$ = new TermType($3, $2, $5); }
        ;

/* yields: ASTList<PrecSpec> */
Precedence: /* empty */                      { $$ = new ASTList<PrecSpec>; }
          | "precedence" "{" PrecSpecs "}"   { $$ = $3; }
          ;

/* yields: ASTList<PrecSpec> */
PrecSpecs: /* empty */
             { $$ = new ASTList<PrecSpec>; }
         | PrecSpecs TOK_NAME TOK_INTEGER NameOrStringList ";"
             { ($$=$1)->append(new PrecSpec(whichKind($2), $3, $4)); }
         ;

/* yields: ASTList<LocString> */
NameOrStringList: /* empty */                     { $$ = new ASTList<LocString>; }
                | NameOrStringList NameOrString   { ($$=$1)->append($2); }
                ;

/* yields: LocString */
NameOrString: TOK_NAME       { $$ = $1; }
            | TOK_STRING     { $$ = $1; }
            ;


/* ------ specification functions ------ */
/* yields: ASTList<SpecFunc> */
SpecFuncs: /* empty */                { $$ = new ASTList<SpecFunc>; }
         | SpecFuncs SpecFunc         { ($$=$1)->append($2); }
         ;

/* yields: SpecFunc */
SpecFunc: TOK_FUN TOK_NAME "(" FormalsOpt ")" TOK_LIT_CODE
            { $$ = new SpecFunc($2, $4, $6); }
        ;

/* yields: ASTList<LocString> */
FormalsOpt: /* empty */               { $$ = new ASTList<LocString>; }
          | Formals                   { $$ = $1; }
          ;

/* yields: ASTList<LocString> */
Formals: TOK_NAME                     { $$ = new ASTList<LocString>($1); }
       | Formals "," TOK_NAME         { ($$=$1)->append($3); }
       ;


/* ------ nonterminals ------ */
/*
 * a nonterminal is a grammar symbol that appears on the LHS of forms;
 * the body of the Nonterminal declaration specifies the the RHS forms,
 * attribute info, etc.
 */
/* yields: TopForm (always TF_nonterm) */
Nonterminal: "nonterm" Type TOK_NAME Production
               { $$ = new TF_nonterm($3, $2, new ASTList<SpecFunc>,
                                     new ASTList<ProdDecl>($4), NULL); }
           | "nonterm" Type TOK_NAME "{" SpecFuncs Productions Subsets "}"
               { $$ = new TF_nonterm($3, $2, $5, $6, $7); }
           ;

/* yields: ASTList<ProdDecl> */
Productions: /* empty */                   { $$ = new ASTList<ProdDecl>; }
           | Productions Production        { ($$=$1)->append($2); }
           ;

/* yields: ProdDecl */
Production: "->" RHS Action                { $$ = new ProdDecl($1, PDK_NEW, $2, $3); }
          | "error" "->" RHS Action        { $$ = new ProdDecl($2, PDK_ERROR, $3, $4); }
          | "replace" "->" RHS Action      { $$ = new ProdDecl($2, PDK_REPLACE,$3, $4); }
          | "delete" "->" RHS ";"          { $$ = new ProdDecl($2, PDK_DELETE, $3, nolocNULL()); }
          ;

/* yields: LocString */
Action: TOK_LIT_CODE                       { $$ = $1; }
      | ";"                                { $$ = nolocNULL(); }
      ;

/* yields: ASTList<RHSElt> */
RHS: /* empty */                           { $$ = new ASTList<RHSElt>; }
   | RHS RHSElt                            { ($$=$1)->append($2); }
   ;

/*
 * each element on the RHS of a form can have a tag, which appears before a
 * colon (':') if present; the tag is required if that symbol's attributes
 * are to be referenced anywhere in the actions or conditions for the form
 */
/* yields: RHSElt */
RHSElt: TOK_NAME                { $$ = new RH_name(sameloc($1, ""), $1); }
      | TOK_NAME ":" TOK_NAME   { $$ = new RH_name($1, $3); }
      | TOK_STRING              { $$ = new RH_string(sameloc($1, ""), $1); }
      | TOK_NAME ":" TOK_STRING { $$ = new RH_string($1, $3); }
       | "precedence" "(" NameOrString ")"    { $$ = new RH_prec($3); }
      | "forbid_next" "(" NameOrString ")"   { $$ = new RH_forbid($3); }
      ;
        
/* yields: ASTList<LocString> */
Subsets: /*empty*/                  { $$ = NULL; }
       | "subsets" Formals ";"      { $$ = $2; }
       ;


%%
/* ------------------ extra C code ------------------ */
AssocKind whichKind(LocString * /*owner*/ kind)
{ 
  // delete 'kind' however we exit
  Owner<LocString> killer(kind);
  
  #define CHECK(syntax, value)   \
    if (kind->equals(syntax)) {  \
      return value;              \
    }
  CHECK("left", AK_LEFT);
  CHECK("right", AK_RIGHT);
  CHECK("nonassoc", AK_NONASSOC);
  CHECK("prec", AK_NEVERASSOC);
  CHECK("assoc_split", AK_SPLIT);
  #undef CHECK

  xbase(stringc << kind->locString()
                << ": invalid associativity kind: " << *kind);
}
