// baselexer.h            see license.txt for copyright and terms of use
// flex-lexer base class; used by C/C++ lexer, among others.
//
// The key property that differentiates baselexer from lexer is
// that the latter knows the details of what tokens exist and
// what their semantic values mean, whereas the former does not.
// Therefore, I can re-use baselexer for other languages, and
// let lexer be the C++-specific one.

#ifndef BASELEXER_H
#define BASELEXER_H

#include "sm_flexlexer.h"   // yyFlexLexer

#include "lexerint.h"       // LexerInterface
#include "strtable.h"       // StringRef, StringTable


// lexer object
class BaseLexer : public yyFlexLexer, public LexerInterface {
protected:  // data
  istream *inputStream;            // (owner) file from which we're reading
  SourceLocManager::File *srcFile; // (serf) contains the hash map we update

  SourceLoc nextLoc;               // location of *next* token
  int curLine;                     // current line number; needed for #line directives

public:     // data
  StringTable &strtable;           // string table
  int errors;                      // count of errors encountered
  int warnings;                    // same for warnings

private:    // funcs
  BaseLexer(BaseLexer&);           // disallowed

protected:  // funcs
  // advance source location
  void updLoc() {
    loc = nextLoc;                 // location of *this* token
    nextLoc = advText(nextLoc, yytext, yyleng);
  }

  // adds a string with only the specified # of chars; writes (but
  // then restores) a null terminator if necessary, so 'str' isn't const
  StringRef addString(char *str, int len);

  // updLoc(), then for every newline found in
  // [yytext,yytext+yyleng-1], increment 'curLine'
  void whitespace();

  // return the given token code, after updLoc'ing and setting
  // 'sval' to NULL; suitable for tokens with one spelling (or
  // otherwise have no semantic value)
  int tok(int t);

  // report an error
  void err(char const *msg);
  void warning(char const *msg);

  // part of the constructor
  istream *openFile(char const *fname);
  istream *openString(char const *buf, int len);

  // read the next token and return its code; returns 0 for end of file;
  // this function is defined in flex's output source code
  //virtual int yylex();
  //
  // since Flex outputs yylex as being a member function of the
  // final lexer class, the declaration of 'yylex' must be put into
  // that class, not this one

public:     // funcs
  // make a lexer to scan the given file
  BaseLexer(StringTable &strtable, char const *fname);
  
  // make a lexer to scan an in-memory string; 'initLoc' is the
  // location that the first character should be regarded as being at;
  // the buffer must remain allocated as long as this BaseLexer is
  BaseLexer(StringTable &strtable, SourceLoc initLoc,
            char const *buf, int len);

  ~BaseLexer();

  static void tokenFunc(LexerInterface *lex);

  // LexerInterface funcs
  virtual NextTokenFunc getTokenFunc() const;
};


// this macro declares the methods that flex's output implements
#define FLEX_OUTPUT_METHOD_DECLS               \
  virtual int yylex();                         \
  yy_state_type yy_get_previous_state();       \
  yy_state_type yy_try_NUL_trans( yy_state_type current_state );



#endif // BASELEXER_H
