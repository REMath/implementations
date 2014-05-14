// trivlex.cc            see license.txt for copyright and terms of use
// trivial lexer (returns each character as a token)
  
#include "lexer2.h"     // Lexer2
#include "syserr.h"     // xsyserror

#include <stdio.h>      // FILE stuff

void trivialLexer(char const *fname, Lexer2 &dest)
{
  FILE *fp = fopen(fname, "r");
  if (!fp) {
    xsyserror("open", fname);
  }                    
  SourceLoc loc = sourceLocManager->encodeBegin(fname);

  int ch;
  while ((ch = fgetc(fp)) != EOF) {
    // abuse Lexer2 to hold chars
    Lexer2Token *tok = new Lexer2Token((Lexer2TokenType)ch, loc);

    // add it to list
    dest.addToken(tok);
                                         
    char aChar = ch;
    loc = sourceLocManager->advText(loc, &aChar, 1);
  }
  dest.addEOFToken();
}
