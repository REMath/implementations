// lexer.cc            see license.txt for copyright and terms of use
// code for lexer.h

#include "lexer.h"       // this module
#include "cc_lang.h"     // CCLang

#include <ctype.h>       // isdigit
#include <stdlib.h>      // atoi


/* 
 * Note about nonseparating tokens and the 'checkForNonsep' function:
 *
 * To diagnose and report erroneous syntax like "0x5g", which would
 * naively be parsed as "0x5" and "g" (two legal tokens), I divide
 * all tokens into two classes: separating and nonseparating.
 *
 * Separating tokens are allowed to be adjacent to each other and
 * to nonseparating tokens.  An example is "(".
 *
 * Nonseparating tokens are not allowed to be adjacent to each other.
 * They must be separated by either whitespace, or at least one
 * separating token.  The nonseparating tokens are identifiers,
 * alphabetic keywords, and literals.  The lexer would of course never
 * yield two adjacent keywords, due to maximal munch, but classifying 
 * such an event as an error is harmless.
 * 
 * By keeping track of whether the last token yielded is separating or
 * not, we'll see (e.g.) "0x5g" as two consecutive nonseparating tokens,
 * and can report that as an error.
 *
 * The C++ standard is rather vague on this point as far as I can
 * tell.  I haven't checked the C standard.  In the C++ standard,
 * section 2.6 paragraph 1 states:
 *
 *  "There are five kinds of tokens: identifiers, keywords, literals,
 *   operators, and other separators.  Blanks, horizontal and
 *   vertical tabs, newlines, formfeeds, and comments (collectively,
 *   "whitespace"), as described below, are ignored except as they
 *   serve to separate tokens.  [Note: Some white space is required
 *   to separate otherwise adjacent identifiers, keywords, numeric
 *   literals, and alternative tokens containing alphabetic
 *   characters.]"
 *
 * The fact that the restriction is stated only in a parenthetical note
 * is of course nonideal.  I think the qualifier "numeric" on "literals"
 * is a mistake, otherwise "a'b'" would be a legal token sequence.  I
 * do not currently implement the "alternative tokens".
 *
 * Update: Mozilla includes things like "foo""bar", i.e. directly
 * adjacent string literals.  Therefore I'm going to interpret (the
 * note in) the standard literally, and take char and string literals
 * to be separating.
 */

// bhackett: file normalization

char *g_working_directory = NULL;
char *g_normalize_directory = NULL;

// remove uses of '.' from a string (except any leading '.').
void CleanupPathDot(char *pos)
{
  char *old = pos;
  while (true) {
    pos = strchr(pos, '/');
    if (pos == NULL)
      break;

    if (pos[1] == '.' && pos[2] == '/') {
      strcpy(pos, &pos[2]);
      pos = old;
    }
    else {
      pos++;
    }
  }
}

// remove uses of '..' from a string (except any leading '..').
void CleanupPathDotDot(char *pos)
{
  char *old = pos;
  while (true) {
    pos = strchr(pos, '/');
    if (pos == NULL)
      break;

    char *next_pos = strchr(pos + 1, '/');
    if (next_pos == NULL)
      break;;

    if (next_pos[1] == '.' && next_pos[2] == '.' && next_pos[3] == '/') {
      strcpy(pos, &next_pos[3]);
      pos = old;
    }
    else {
      pos++;
    }
  }
}

char* GetNormalizedFile(const char *file)
{
  // compute the absolute filename. yeah we're not checking bounds here.
  char buf[10000];
  char *pos = buf;

  if (file[0] == '/') {
    // the supplied filename is already an absolute path, use that.
    strcpy(pos, file);
  }
  else if (file[0] == '<') {
    // special compiler name, use it (we won't have the original source).
    strcpy(pos, file);
  }
  else if (g_working_directory) {
    // relative path from the working directory.
    strcpy(pos, g_working_directory);
    pos += strlen(g_working_directory);
    *pos++ = '/';
    strcpy(pos, file);
  }
  else {
    // give up.
    strcpy(pos, file);
  }

  CleanupPathDot(buf);
  CleanupPathDotDot(buf);

  // remove the specified normalized directory prefix, if possible.
  if (g_normalize_directory) {
    size_t normalize_len = strlen(g_normalize_directory);
    if (strncmp(buf, g_normalize_directory, normalize_len) == 0) {
      Assert(buf[normalize_len] == '/');
      char *pos = buf + normalize_len + 1;
      return strdup(pos);
    }
  }

  return strdup(buf);
}




// -------------------- TokenType ---------------------
// these aren't emitted into cc_tokens.cc because doing so would
// make that output dependent on smbase/xassert.h
char const *toString(TokenType type)
{
  xassert(NUM_TOKEN_TYPES == tokenNameTableSize);
  xassert((unsigned)type < (unsigned)NUM_TOKEN_TYPES);
  return tokenNameTable[type];
}

TokenFlag tokenFlags(TokenType type)
{
  xassert((unsigned)type < (unsigned)NUM_TOKEN_TYPES);
  return (TokenFlag)tokenFlagTable[type];
}


// ------------------------ Lexer -------------------
Lexer::Lexer(StringTable &s, CCLang &L, char const *fname)
  : BaseLexer(s, fname),

    prevIsNonsep(false),
    prevHashLineFile(s.add(fname)),

    lang(L)
{
  // prime this lexer with the first token
  getTokenFunc()(this);
}


Lexer::Lexer(StringTable &s, CCLang &L, SourceLoc initLoc,
             char const *buf, int len)
  : BaseLexer(s, initLoc, buf, len),

    prevIsNonsep(false),
    prevHashLineFile(s.add(sourceLocManager->getFile(initLoc))),

    lang(L)
{
  // do *not* prime the lexer; I think it is a mistake above, but
  // am leaving it for now
}


Lexer::~Lexer()
{}


void Lexer::whitespace()
{
  BaseLexer::whitespace();

  // various forms of whitespace can separate nonseparating tokens
  prevIsNonsep = false;
}


// this, and 'svalTok', are out of line because I don't want the
// yylex() function to be enormous; I want that to just have a bunch
// of calls into these routines, which themselves can then have
// plenty of things inlined into them
int Lexer::tok(TokenType t)
{
  checkForNonsep(t);
  updLoc();
  sval = NULL_SVAL;     // catch mistaken uses of 'sval' for single-spelling tokens
  return t;
}


int Lexer::svalTok(TokenType t) 
{
  checkForNonsep(t);
  updLoc();
  sval = (SemanticValue)addString(yytext, yyleng);
  return t;
}


int Lexer::alternateKeyword_tok(TokenType t)
{
  if (lang.isCplusplus) {
    return tok(t);
  }
  else {
    // in C mode, they are just identifiers
    return svalTok(TOK_NAME);
  }
}

// examples of recognized forms
//   #line 4 "foo.cc"       // canonical form
//   # 4 "foo.cc"           // "line" can be omitted
//   # 4 "foo.cc" 1         // extra stuff is ignored
//   # 4                    // omitted filename means "same as previous"
void Lexer::parseHashLine(char *directive, int len)
{
  char *endp = directive+len;

  directive++;        // skip "#"
  if (*directive == 'l') {
    directive += 4;   // skip "line"
  }

  // skip whitespace
  while (*directive==' ' || *directive=='\t') {
    directive++;
  }

  // parse the line number
  if (!isdigit(*directive)) {
    pp_err("malformed #line directive line number");
    return;
  }
  int lineNum = atoi(directive);

  // skip digits and whitespace
  while (isdigit(*directive)) {
    directive++;
  }
  while (*directive==' ' || *directive=='\t') {
    directive++;
  }

  if (*directive == '\n') {
    // no filename: use previous
    srcFile->addHashLine(curLine, lineNum, prevHashLineFile);
    return;
  }

  if (*directive != '\"') {
    pp_err("#line directive missing leading quote on filename");
    return;
  }
  directive++;

  // look for trailing quote
  char *q = directive;
  while (q<endp && *q != '\"') {
    q++;
  }
  if (*q != '\"') {
    pp_err("#line directive missing trailing quote on filename");
    return;
  }

  // temporarily write a NUL so we can make a StringRef
  *q = 0;

  // use the normalized name.
  char *fname_cstr = GetNormalizedFile(directive);
  StringRef fname = strtable.add(fname_cstr);
  free(fname_cstr);

  *q = '\"';

  // remember this directive
  srcFile->addHashLine(curLine, lineNum, fname);

  // remember the filename for future #line directives that
  // don't explicitly include one
  prevHashLineFile = fname;
}


// preprocessing error: report the location information in the
// preprocessed source, ignoring #line information
void Lexer::pp_err(char const *msg)
{
  // print only line information, and subtract one because I account
  // for whitespace (including the final newline) before processing it
  errors++;
  cerr << srcFile->name << ":" << (curLine-1) << ": error: " << msg << endl;
}


STATICDEF void Lexer::tokenFunc(LexerInterface *lex)
{
  Lexer *ths = static_cast<Lexer*>(lex);

  // call into the flex lexer; this updates 'loc' and sets
  // 'sval' as appropriate
  ths->type = ths->yylex();
}


STATICDEF void Lexer::c_tokenFunc(LexerInterface *lex)
{
  // as above
  Lexer *ths = static_cast<Lexer*>(lex);
  ths->type = ths->yylex();

  // map C++ keywords into identifiers
  TokenType tt = (TokenType)(ths->type);
  if (tokenFlags(tt) & TF_CPLUSPLUS) {
    // create the lexeme corresponding to the token's spelling
    StringRef str = ths->strtable.add(toString(tt));
    
    // set the LexerInterface fields to yield the new token
    ths->type = TOK_NAME;
    ths->sval = (SemanticValue)str;
  }
}


Lexer::NextTokenFunc Lexer::getTokenFunc() const
{
  if (lang.recognizeCppKeywords) {
    // expected case, yield the normal tokenizer
    return &Lexer::tokenFunc;                   
  }
  else {
    // yield the tokenizer that maps C++ keywords into C keywords
    return &Lexer::c_tokenFunc;
  }
}

string Lexer::tokenDesc() const
{
  if (tokenFlags((TokenType)type) & TF_MULTISPELL) {
    // for tokens with multiple spellings, decode 'sval' as a
    // StringRef
    //return string((StringRef)sval);
    return stringc << toString((TokenType)type) << ": " << (StringRef)sval;
  }
  else {
    // for all others, consult the static table
    return string(toString((TokenType)type));
  }
}

string Lexer::tokenKindDesc(int kind) const
{
  // static table only
  return toString((TokenType)kind);
}


// EOF
