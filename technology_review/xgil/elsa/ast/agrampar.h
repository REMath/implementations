// agrampar.h            see license.txt for copyright and terms of use
// declarations for things that the bison-generated parser uses

#ifndef AGRAMPAR_H
#define AGRAMPAR_H

#include "ast.hand.h"       // AST node class declarations
#include "str.h"            // string

class GrammarLexer;

// ---------------- agrampar's view of the parser --------------------
// name of extra parameter to yyparse (i.e. the context in
// which the parser operates, instead of that being stored
// in some collection of globals)
#define YYPARSE_PARAM parseParam

// type of thing extra param points at
struct ASTParseParams {
  ASTSpecFile *treeTop;       // set when parsing finishes; AST tree top
  GrammarLexer &lexer;        // lexer we're using

public:
  ASTParseParams(GrammarLexer &L) :
    treeTop(NULL),
    lexer(L)
  {}
};

// caller interface to Bison-generated parser; starts parsing
// (whatever stream lexer is reading) and returns 0 for success and
// 1 for error; the extra parameter is available to actions to use
#define YYPARSE_PARAM parseParam
int agrampar_yyparse(void *YYPARSE_PARAM);

// when this is set to true, bison parser emits info about
// actions as it's taking them
extern int yydebug;


// ---------- parser's view of the rest of the program -----------
// return contents of 's', which is then deallocated
string unbox(string *s);

// box 's' as a string object
string *box(char const *s);

// return concatenation of two strings; source strings are deallocated
string *appendStr(string *left, string *right);

// parse a string into components
CtorArg *parseCtorArg(rostring str);

// error routine
void agrampar_yyerror(char const *msg, void *parseParam);
#define yyerror(m) agrampar_yyerror(m, YYPARSE_PARAM)

// parser's view of the lexer
int agrampar_yylex(union YYSTYPE *lvalp, void *parseParam);
#define yylex agrampar_yylex
#define YYLEX_PARAM parseParam

// classify token codes
bool isAGramlexEmbed(int code);


// --------------- external interface to agrampar ---------------
ASTSpecFile *readAbstractGrammar(char const *fname);


#endif // AGRAMPAR_H
