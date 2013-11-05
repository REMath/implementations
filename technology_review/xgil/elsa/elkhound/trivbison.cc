// trivbison.cc            see license.txt for copyright and terms of use
// driver file for a Bison-parser with the trivial lexer

#include "trivbison.h"  // this module
#include "lexer2.h"     // Lexer2
#include "trivlex.h"    // trivialLexer
#include "trace.h"      // traceProgress
#include "syserr.h"     // xsyserror
#include "ptreenode.h"  // PTreeNode
#include "cyctimer.h"   // CycleTimer

#include <stdio.h>      // printf

// global list of L2 tokens for yielding to Bison
Lexer2 lexer2;
Lexer2Token const *lastTokenYielded = NULL;

// parsing entry point
int yyparse();

// returns token types until EOF, at which point L2_EOF is returned
int yylex()
{
  static ObjListIter<Lexer2Token> *iter = NULL;

  if (!iter) {
    // prepare to return tokens
    iter = new ObjListIter<Lexer2Token>(lexer2.tokens);
  }

  if (!iter->isDone()) {
    // grab type to return
    lastTokenYielded = iter->data();
    Lexer2TokenType ret = iter->data()->type;

    // advance to next token
    iter->adv();

    // return one we just advanced past
    return ret;
  }
  else {
    // done; don't bother freeing things
    lastTokenYielded = NULL;
    return L2_EOF;
  }
}


void yyerror(char const *s)
{
  if (lastTokenYielded) {
    printf("%s: ", lastTokenYielded->loc.toString().pcharc());
  }
  else {
    printf("<eof>: ");
  }
  printf("%s\n", s);
}


int main(int argc, char *argv[])
{
  char const *progname = argv[0];

  if (argc >= 2 &&
      0==strcmp(argv[1], "-d")) {
    #ifdef YYDEBUG
      yydebug = 1;
    #else
      printf("debugging is disabled because YYDEBUG isn't set\n");
      return 2;
    #endif

    argc--;
    argv++;
  }

  if (argc < 2) {
    printf("usage: %s [-d] inputfile\n", progname);
    printf("  -d: turn on yydebug, so it prints shift/reduce actions\n");
    return 0;
  }

  char const *inputFname = argv[1];

  traceAddSys("progress");

  // run lexer
  traceProgress() << "lexical analysis...\n";
  trivialLexer(inputFname, lexer2);

  // start Bison-parser
  traceProgress() << "starting parse..." << endl;
  CycleTimer timer;

  if (yyparse() != 0) {
    cout << "yyparse returned with an error\n";
  }

  traceProgress() << "finished parse (" << timer.elapsed() << ")" << endl;

  cout << "tree nodes: " << PTreeNode::allocCount
       << endl;

  return 0;
}
