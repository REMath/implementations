// parssppt.h            see license.txt for copyright and terms of use
// parser-support routines, for use at runtime while processing
// the generated Parse tree
//
// this module is primarily for use with the C and C++ grammars,
// but has been pressed into service for a few other uses too;
// new grammars and parsers should probably not use this



//                  alt.parssppt.die.die.die!

// TODO:  This is a stupid module: ill-conceived, and awkward to use.
// It either needs to be rewritten, or its functionality spread to
// other modules.



#ifndef PARSSPPT_H
#define PARSSPPT_H

#include "lexer.h"        // Lexer
#include "useract.h"      // SemanticValue, UserAction

class ParseTables;
class GLR;
class LexerInterface;


// ----------------- helpers for analysis drivers ---------------
// a self-contained parse tree (or parse DAG, as the case may be)
class ParseTreeAndTokens {
public:
  // reference to place to store final semantic value
  SemanticValue &treeTop;

  // just replacing Lexer2 with Lexer for now..
  LexerInterface *lexer;           // (owner)

  // parse parameter
  UserActions *userAct;            // (serf)

  // parse tables (or NULL)
  ParseTables *tables;             // (serf)

  // receives the parse error count from the GLR parser.
  int errors;

public:
  ParseTreeAndTokens(CCLang &lang, SemanticValue &top, StringTable &extTable,
                     char const *inputFname);
  ~ParseTreeAndTokens();
};


void glrParseNamedFile(GLR &glr, LexerInterface &lexer, SemanticValue &treeTop,
                       char const *inputFname);

void toplevelParse(ParseTreeAndTokens &ptree, char const *inputFname);

char *processArgs(int argc, char **argv, char const *additionalInfo = NULL);

void maybeUseTrivialActions(ParseTreeAndTokens &ptree);

// useful for simple treewalkers; false on error
bool treeMain(ParseTreeAndTokens &ptree, int argc, char **argv,
              char const *additionalInfo = NULL);


#endif // PARSSPPT_H
