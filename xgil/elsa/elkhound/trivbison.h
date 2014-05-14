// trivbison.h            see license.txt for copyright and terms of use
// decls shared between trivbison.cc and EFa.*tree.y
// originally created by copying bccgr.h

#ifndef TRIVBISON_H
#define TRIVBISON_H

#include <stdlib.h>     // free

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

// functions called by Bison-parser
void yyerror();
int yylex();

// Bison-parser entry
int yyparse();
extern int yydebug;
       
#ifdef __cplusplus
}
#endif // __cplusplus

#endif // TRIVBISON_H
