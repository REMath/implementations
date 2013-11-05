// tlexer.cc            see license.txt for copyright and terms of use
// test the lexer alone

#include "lexer.h"         // Lexer
#include "strtable.h"      // StringTable
#include "cc_lang.h"       // CCLang
#include "test.h"          // ARGS_MAIN
#include "nonport.h"       // getMilliseconds
#include "trace.h"         // tracingSys


void entry(int argc, char **argv)
{
  char const *progName = argv[0];
  TRACE_ARGS()

  if (argc != 2) {
    cout << "usage: " << progName << " [-tr tokens] input.i\n";
    return;
  }
  traceAddSys("progress");

  StringTable table;
  CCLang lang;
  lang.ANSI_Cplusplus();     // want 'true' and 'false' keywords
  SourceLocManager mgr;

  traceProgress() << "making Lexer\n";
  Lexer lexer(table, lang, argv[1]);
  Lexer::NextTokenFunc nextToken = lexer.getTokenFunc();

  bool print = tracingSys("tokens");

  traceProgress() << "lexing " << argv[1] << "...\n";
  long start = getMilliseconds();

  while (lexer.type != 0 /*eof*/) {
    if (print) {
      cout << toString(lexer.loc) << ": " << lexer.tokenDesc() << endl;
    }

    nextToken(&lexer);
  }

  traceProgress() << "done lexing (" << (getMilliseconds() - start)
                  << " ms)\n";
}

ARGS_MAIN
