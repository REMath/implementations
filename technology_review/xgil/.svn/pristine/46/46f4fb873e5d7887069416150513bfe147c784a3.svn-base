// ssxmain.cc            see license.txt for copyright and terms of use
// main() for use with SSx.tree.gr

#include "trivlex.h"   // trivialLexer
#include "parssppt.h"  // ParseTreeAndTokens
#include "test.h"      // ARGS_MAIN
#include "trace.h"     // TRACE_ARGS
#include "glr.h"       // GLR
#include "useract.h"   // UserActions
#include "ptreenode.h" // PTrdeeNode


#if 0     // obsolete, replaced by ptreenode.cc
TreeCount count(Node *n)
{
  // memoize to avoid exponential blowup
  if (n->count != 0) {
    return n->count;
  }

  switch (n->type) {
    default:
      xfailure("bad code");

    case Node::MERGE:
      // a single tree can take either from the left or
      // the right, but not both simultaneously
      n->count = count(n->left) + count(n->right);
      break;

    case Node::SSX:
      // a single tree can have any possibility from left
      // and any possibility from right
      n->count = count(n->left) * count(n->right);
      break;

    case Node::X:
      n->count = 1;
      break;
  }

  return n->count;
}
#endif // 0


// compute the sum at the top of SSx.tree.gr
TreeCount C(int n)
{
  static TreeCount *memoized = NULL;
  if (!memoized) {
    memoized = new TreeCount[n+1];

    memoized[0] = 1;      // seed value: C(0)=1

    for (int i=1; i<n+1; i++) {
      memoized[i] = 0;    // entry hasn't been computed yet
    }
  }

  if (memoized[n]) {
    return memoized[n];
  }

  TreeCount sum = 0;
  for (int m=0; m<n; m++) {
    sum += C(m) * C(n-1-m);
  }

  memoized[n] = sum;
  return sum;
}


// defined in the grammar file
UserActions *makeUserActions();

int entry(int argc, char *argv[])
{
  char const *progName = argv[0];
  TRACE_ARGS();

  if (argc < 2) {
    printf("usage: %s input-file\n", progName);
    return 0;
  }
  char const *inputFname = argv[1];

  // see how long the input is
  int inputLen;
  {
    FILE *input = fopen(inputFname, "r");
    if (!input) {
      printf("cannot open file: %s\n", inputFname);
      return 2;
    }
    fseek(input, 0, SEEK_END);
    inputLen = ftell(input);
    fclose(input);
  }

  // lex input
  Lexer2 lexer;
  trivialLexer(inputFname, lexer);

  // setup parser
  UserActions *user = makeUserActions();
  GLR glr(user);
  glr.readBinaryGrammar("SSx.tree.bin");

  // parse input
  SemanticValue treeTop;
  if (!glr.glrParse(lexer, treeTop)) {
    // glrParse prints the error itself
    return 2;
  }

  // count # of parses
  PTreeNode *top = (PTreeNode*)treeTop;
  TreeCount numParses = top->countTrees();
  cout << "num parses: " << numParses << endl;

  // print what it should be
  int n = (inputLen - 1) / 2;
  cout << "input is x^" << inputLen 
       << "; C(" << n 
       << ") = " << C(n)
       << endl;

  return 0;
}


ARGS_MAIN
