// iptparse.h
// interface to the interval partition tree parser

#ifndef IPTPARSE_H
#define IPTPARSE_H

#include <stdio.h>    // FILE
#include "str.h"      // rostring

class IPTree;         // iptree.h

// the lexer stashes lexed integer codes here
extern int lexerSval;

// token codes
enum TokenType {
  TOK_EOF=0,          // end of file
  TOK_INTLIT,         // integer literal
  TOK_COMMA,          // ","
  TOK_SEMICOLON,      // ";"

  NUM_TOKENTYPES
};

// call this to begin lexing (defined in iptparse.yy.cc)
void yyrestart(FILE *input_file);

// call this to get the next token (defined in iptparse.yy.cc)
TokenType getNextToken();

// parse a file into a given tree
IPTree *parseFile(rostring fname);


#endif // IPTPARSE_H
