// trivmain.cc            see license.txt for copyright and terms of use
// main() for use with trivlex, and grammars which just test
// parsing properties

#ifndef GRAMMAR_NAME
  #error set preprocessor symbol GRAMMAR_NAME to the name of the .bin grammar file
#endif

#include "trivlex.h"   // trivialLexer
#include "test.h"      // ARGS_MAIN
#include "trace.h"     // TRACE_ARGS
#include "useract.h"   // TrivialUserActions
#include "lexer2.h"    // Lexer2
#include "glr.h"       // GLR
#include "useract.h"   // UserActions
#include "ptreenode.h" // PTreeNode
#include "cc_lang.h"   // CCLang
#include "exc.h"       // throw_XOpen

#include <string.h>    // strcmp
#include <stdlib.h>    // exit

// no bison-parser present, so need to define this
Lexer2Token const *yylval = NULL;


// compute the sum at the top of SSx.gr.in
TreeCount ssxCount(int n)
{
  static TreeCount *memoized = NULL;
  if (!memoized) {
    memoized = new TreeCount[n+1];

    memoized[0] = 1;      // seed value: ssxCount(0)=1

    for (int i=1; i<n+1; i++) {
      memoized[i] = 0;    // entry hasn't been computed yet
    }
  }

  if (memoized[n]) {
    return memoized[n];
  }

  TreeCount sum = 0;
  for (int m=0; m<n; m++) {
    sum += ssxCount(m) * ssxCount(n-1-m);
  }

  memoized[n] = sum;
  return sum;
}


// compute the sum at the top of SSSx.gr.in
TreeCount sssxCount(int n)
{
  static TreeCount *memoized = NULL;
  if (!memoized) {
    memoized = new TreeCount[n+1];

    memoized[1] = 1;      // seed value: sssxCount(1)=1

    for (int i=2; i<n+1; i++) {
      memoized[i] = 0;    // entry hasn't been computed yet
    }
  }

  xassert(n > 0);

  if (memoized[n]) {
    return memoized[n];
  }

  TreeCount sum = sssxCount(n-1);

  for (int m = 1; m <= n-3; m++) {
    for (int p = 1; m+p <= n-2; p++) {
      int q = n-1 - m - p;
      xassert(q > 0);

      sum += sssxCount(m) * sssxCount(p) * sssxCount(q);
    }
  }

  memoized[n] = sum;
  return sum;
}


// defined in the grammar file
UserActions *makeUserActions();

void entry(int argc, char *argv[])
{
  char const *progName = argv[0];
  TRACE_ARGS();

  if (argc < 2) {
    printf("usage: %s [-tr flags] [-count] input-file\n", progName);
    return;
  }

  bool count = false;
  if (0==strcmp(argv[1], "-count")) {
    count = true;
    argv++;    // shift
    argc--;
  }

  SourceLocManager mgr;

  char const *inputFname = argv[1];

  // see how long the input is
  int inputLen;
  {
    FILE *input = fopen(inputFname, "r");
    if (!input) {
      throw_XOpen(inputFname);
    }
    fseek(input, 0, SEEK_END);
    inputLen = ftell(input);
    fclose(input);
  }

  // lex input
  CCLang lang;
  Lexer2 lexer(lang);
  traceProgress() << "lexing...\n";
  trivialLexer(inputFname, lexer);
  lexer.beginReading();

  // set up parser
  UserActions *user = makeUserActions();
  ParseTables *tables = user->makeTables();

  // possibly replace actions with trivial ones
  if (tracingSys("trivialActions")) {
    user = new TrivialUserActions();
    count = false;   // cannot count with trivial actions, because no tree is made
  }

  // make the parser object
  GLR glr(user, tables);

  // parse input
  SemanticValue treeTop;
  if (!glr.glrParse(lexer, treeTop)) {
    // glrParse prints the error itself
    exit(2);
  }

  PTreeNode *top = (PTreeNode*)treeTop;

  // count # of parses
  if (count) {
    TreeCount numParses = top->countTrees();
    cout << "num parses: " << numParses << endl;

    TreeCount should = 0;    // meaning unknown
    if (0==strcmp(GRAMMAR_NAME, "triv/SSx.tree.bin")) {
      should = ssxCount((inputLen-1) / 2);
    }
    if (0==strcmp(GRAMMAR_NAME, "triv/SSSx.tree.bin")) {
      should = sssxCount(inputLen);
    }

    if (should != 0) {
      cout << "should be: " << should << endl;
      if (should != numParses) {
        cout << "MISMATCH in number of parse trees\n";
      }
    }
  }
  cout << "tree nodes: " << PTreeNode::allocCount
       << endl;

  if (tracingSys("printTree")) {
    top->printTree(cout);
  }
}


ARGS_MAIN
