/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton interface for Bison's Yacc-like parsers in C

   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor,
   Boston, MA 02110-1301, USA.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     TOK_INTEGER = 258,
     TOK_NAME = 259,
     TOK_STRING = 260,
     TOK_LIT_CODE = 261,
     TOK_LBRACE = 262,
     TOK_RBRACE = 263,
     TOK_COLON = 264,
     TOK_SEMICOLON = 265,
     TOK_ARROW = 266,
     TOK_LPAREN = 267,
     TOK_RPAREN = 268,
     TOK_COMMA = 269,
     TOK_TERMINALS = 270,
     TOK_TOKEN = 271,
     TOK_NONTERM = 272,
     TOK_FUN = 273,
     TOK_VERBATIM = 274,
     TOK_IMPL_VERBATIM = 275,
     TOK_PRECEDENCE = 276,
     TOK_OPTION = 277,
     TOK_EXPECT = 278,
     TOK_CONTEXT_CLASS = 279,
     TOK_SUBSETS = 280,
     TOK_DELETE = 281,
     TOK_REPLACE = 282,
     TOK_FORBID_NEXT = 283,
     TOK_ERROR = 284
   };
#endif
/* Tokens.  */
#define TOK_INTEGER 258
#define TOK_NAME 259
#define TOK_STRING 260
#define TOK_LIT_CODE 261
#define TOK_LBRACE 262
#define TOK_RBRACE 263
#define TOK_COLON 264
#define TOK_SEMICOLON 265
#define TOK_ARROW 266
#define TOK_LPAREN 267
#define TOK_RPAREN 268
#define TOK_COMMA 269
#define TOK_TERMINALS 270
#define TOK_TOKEN 271
#define TOK_NONTERM 272
#define TOK_FUN 273
#define TOK_VERBATIM 274
#define TOK_IMPL_VERBATIM 275
#define TOK_PRECEDENCE 276
#define TOK_OPTION 277
#define TOK_EXPECT 278
#define TOK_CONTEXT_CLASS 279
#define TOK_SUBSETS 280
#define TOK_DELETE 281
#define TOK_REPLACE 282
#define TOK_FORBID_NEXT 283
#define TOK_ERROR 284




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 105 "grampar.y"
{
  int num;
  LocString *str;
  SourceLoc loc;

  ASTList<TopForm> *topFormList;
  TopForm *topForm;

  ASTList<TermDecl> *termDecls;
  TermDecl *termDecl;
  ASTList<TermType> *termTypes;
  TermType *termType;
  ASTList<PrecSpec> *precSpecs;

  ASTList<SpecFunc> *specFuncs;
  SpecFunc *specFunc;
  ASTList<LocString> *stringList;

  ASTList<ProdDecl> *prodDecls;
  ProdDecl *prodDecl;
  ASTList<RHSElt> *rhsList;
  RHSElt *rhsElt;
}
/* Line 1489 of yacc.c.  */
#line 131 "grampar.tab.h"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif



