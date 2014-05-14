// astxml_lexer.h           see license.txt for copyright and terms of use

#ifndef ASTXML_LEXER_H
#define ASTXML_LEXER_H

#include <stdio.h>

#include "baselexer.h"          // FLEX_OUTPUT_METHOD_DECLS
#include "sm_flexlexer.h"       // yyFlexLexer
#include "str.h"                // string
#include "astxml_tokens.h"

class AstXmlLexer : private yyFlexLexer {
  public:
  char const *inputFname;
  int linenumber;
  bool sawEof;

  AstXmlLexer(char const *inputFname0)
    : inputFname(inputFname0)
    , linenumber(1)             // file line counting traditionally starts at 1
    , sawEof(false)
  {}

  // this is yylex() but does what I want it to with EOF
  int getToken();
  // have we seen the EOF?
  bool haveSeenEof() { return sawEof; }
  // this is yytext
  char const *currentText() { return this->YYText(); }
  // this is yyrestart
  void restart(ifstream *in) { this->yyrestart(in); }

  int tok(ASTXMLTokenType kind);
  int svalTok(ASTXMLTokenType t);
  void err(char const *msg);
  
  string tokenKindDesc(int kind) const;

  FLEX_OUTPUT_METHOD_DECLS
};

#endif // ASTXML_LEXER_H
