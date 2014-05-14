// astxml_lexer.cc         see License.txt for copyright and terms of use

#include "astxml_lexer.h"
#include "xassert.h"
#include "exc.h"


// ------------------------ AstXmlLexer -------------------
static char const * const tokenNames[] = {
  "XTOK_EOF",

  "XTOK_NAME",

  "XTOK_INT_LITERAL",
  "XTOK_FLOAT_LITERAL",
  "XTOK_HEX_LITERAL",
  "XTOK_STRING_LITERAL",

  "XTOK_LESSTHAN",
  "XTOK_GREATERTHAN",
  "XTOK_EQUAL",
  "XTOK_SLASH",

  // tokens for lexing the AST XML
#include "astxml_lexer1_mid.gen.cc"

  // tokens for lexing the typesystem XML
#include "astxml_lexer1_type.cc"

  "NUM_XML_TOKEN_TYPES",
};

int AstXmlLexer::getToken() {
  int token = this->yylex();
  if (token==0) {
    sawEof = true;
  }
  return token;
}

int AstXmlLexer::tok(ASTXMLTokenType kind) {
//    printf("%s\n", tokenKindDesc(kind).c_str());
//    fflush(stdout);
  return kind;
}

int AstXmlLexer::svalTok(ASTXMLTokenType kind)
{
//    printf("%s '%s'\n", tokenKindDesc(kind).c_str(), yytext);
//    fflush(stdout);
  return kind;
}

void AstXmlLexer::err(char const *msg)
{
  THROW(xBase(stringc << inputFname << ":" << linenumber << ":" << msg));
}

string AstXmlLexer::tokenKindDesc(int kind) const
{
  xassert(0 <= kind && kind < NUM_XML_TOKEN_TYPES);
  xassert(tokenNames[kind]);     // make sure the tokenNames array grows with the enum
  return tokenNames[kind];
}
