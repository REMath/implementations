// mlsstr.h            see license.txt for copyright and terms of use
// handles lexically embedded ML
// based on ccsstr.h

#ifndef MLSSTR_H
#define MLSSTR_H

#include "embedded.h"      // EmbeddedLang
#include "array.h"         // ArrayStack

class MLSubstrateTest;

class MLSubstrate : public EmbeddedLang {
private:
  enum State {
    ST_NORMAL,       // normal text
    ST_STRING,       // inside a string literal
    ST_CHAR,         // inside a char literal
    ST_APOSTROPHE1,  // last char was an apostrophe
    ST_APOSTROPHE2,  // char before last was an apostrophe
    NUM_STATES
  } state;
  ArrayStack<char> delims; // stack of paren/bracket/brace delimiters
  int nestingBias;         // modifies the nesting level
  int comNesting;          // depth of comment nesting; 0 means not in comment
  char prev;               // previous character

  // NOTE: Because ocaml wants (**) to be usable to comment out
  // arbitrary code sequences, the comment-ness is mostly orthogonal
  // to other lexing state.  e.g., the syntax (* "(*" *) will be
  // parsed as a (complete) comment.

  // so test code can interrogate internal state
  friend class MLSubstrateTest;

private:
  // depth of delimiter nesting
  int nesting() const { return delims.length() + nestingBias; }
  
  // whether we are in a comment
  bool inComment() const { return comNesting>0; }

public:
  MLSubstrate(ReportError *err = NULL);
  virtual ~MLSubstrate();

  // EmbeddedLang entry points (see gramlex.h for description
  // of each function)
  virtual void reset(int initNest = 0);
  virtual void handle(char const *str, int len, char finalDelim);
  virtual bool zeroNesting() const;
  virtual string getFuncBody() const;
  virtual string getDeclName() const;
};

#endif // MLSSTR_H
