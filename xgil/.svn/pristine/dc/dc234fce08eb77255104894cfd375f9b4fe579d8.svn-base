// iptparse.cc
// (some) code for iptparse.h

#include "iptparse.h"      // this module
#include "iptree.h"        // IPTree
#include "autofile.h"      // AutoFILE
#include "exc.h"           // xfatal

#include <stdlib.h>        // rand()


TokenType lookahead = TOK_EOF;


// get the next token and stash it in 'lookahead'
void getToken()
{
  lookahead = getNextToken();
}
 

// string representation of current token
string tokenToString()
{
  if (lookahead == TOK_INTLIT) {
    return stringc << "intlit(" << lexerSval << ")";
  }
  else {
    static char const * const map[] = {
      "EOF",
      "INTLIT",
      "COMMA",
      "SEMICOLON"
    };

    xassert(TABLESIZE(map) == NUM_TOKENTYPES);
    return string(map[lookahead]);
  }
}


// report parse error at current token
void parseError()
{
  xfatal("parse error at " << tokenToString());
}


// get token and expect it to be a specific kind
void expect(TokenType t)
{
  getToken();
  if (lookahead != t) {
    parseError();
  }
}


void parseBracePair(ArrayStack<Interval> &pairs)
{
  xassert(lookahead == TOK_INTLIT);
  int lo = lexerSval;

  expect(TOK_COMMA);

  expect(TOK_INTLIT);
  int hi = lexerSval;

  expect(TOK_SEMICOLON);

  pairs.push(Interval(lo, hi));
}

                              
// return a random number in [0,n-1], uniformly distributed
static int randomNumber(int n)
{
  // from rand() man page
  return (int)((double)n*rand()/(RAND_MAX+1.0));
}

void shuffleRange(ArrayStack<Interval> &pairs, int lo, int hi)
{
  while (lo < hi) {
    // exchange 'lo' with a random element above it
    int other = lo+1+randomNumber(hi-lo);
    
    // should only be exchanging elements with equal size
    xassert(pairs[lo].size() == pairs[other].size());
                       
    // swap
    Interval tmp = pairs[lo];
    pairs[lo] = pairs[other];
    pairs[other] = tmp;
    
    lo++;
  }
}


static int decSizeCompare(Interval const *a, Interval const *b)
{
  return b->size() - a->size();
}

IPTree *parseFile(rostring fname)
{
  AutoFILE fp(toCStr(fname), "r");
  yyrestart(fp);

  ArrayStack<Interval> pairs;

  bool done = false;
  while (!done) {
    getToken();
    switch (lookahead) {
      case TOK_EOF:
        done = true;
        break;

      case TOK_INTLIT:
        parseBracePair(pairs);
        break;

      default:
        parseError();
    }
  }

  // sort the pairs by decreasing size
  pairs.sort(decSizeCompare);

  // randomize the order of elements with equal sizes
  int lastSize = -1;
  int lastSizeStart = -1;
  int maxHi = 0;
  int i;
  for (i=0; i < pairs.length(); i++) {
    // also calculate the maximum 'hi' value
    if (pairs[i].hi > maxHi) {
      maxHi = pairs[i].hi;
    }

    if (pairs[i].size() != lastSize) {
      if (lastSize > 0) {
        shuffleRange(pairs, lastSizeStart, i-1);
      }

      // new range of equisize intervals
      lastSize = pairs[i].size();
      lastSizeStart = i;
    }
  }

  // last range
  if (lastSize > 0) {
    shuffleRange(pairs, lastSizeStart, i-1);
  }

  // make the tree
  IPTree *tree = new IPTree(maxHi);

  // now insert them in order
  for (i=0; i < pairs.length(); i++) {
    tree->insert(pairs[i].lo, pairs[i].hi);
  }

  return tree;
}


// --------------------- test code ---------------------
#ifdef TEST_IPTPARSE

#include "test.h"      // ARGS_MAIN

void entry(int argc, char *argv[])
{
  xBase::logExceptions = false;

  if (argc < 2) {
    xbase(stringc << "usage: " << argv[0] << " foo.c.str [tree]");
  }

  IPTree *tree = parseFile(argv[1]);

  if (argc >= 3) {
    tree->gdb();
  }

  cout << "link chases: " << Node::linkChases << "\n";
  
  delete tree;
}

ARGS_MAIN

#endif // TEST_IPTPARSE
