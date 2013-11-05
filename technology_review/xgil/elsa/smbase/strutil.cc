// strutil.cc            see license.txt for copyright and terms of use
// code for strutil.h

#include "strutil.h"     // this module
#include "exc.h"         // xformat
#include "autofile.h"    // AutoFILE
#include "array.h"       // Array

#include <ctype.h>       // isspace
#include <string.h>      // strstr, memcmp
#include <stdio.h>       // sprintf
#include <stdlib.h>      // strtoul
#include <time.h>        // time, asctime, localtime


// replace all instances of oldstr in src with newstr, return result
string replace(rostring origSrc, rostring oldstr, rostring newstr)
{
  stringBuilder ret;
  char const *src = toCStr(origSrc);

  while (*src) {
    char const *next = strstr(src, toCStr(oldstr));
    if (!next) {
      ret << src;
      break;
    }

    // add the characters between src and next
    ret << substring(src, next-src);

    // add the replace-with string
    ret << newstr;

    // move src to beyond replaced substring
    src += (next-src) + strlen(oldstr);
  }

  return ret;
}


string expandRanges(char const *chars)
{
  stringBuilder ret;
  
  while (*chars) {
    if (chars[1] == '-' && chars[2] != 0) {
      // range specification
      if (chars[0] > chars[2]) {
        xformat("range specification with wrong collation order");
      }

      for (char c = chars[0]; c <= chars[2]; c++) {
        ret << c;
      }
      chars += 3;
    }
    else {
      // simple character specification
      ret << chars[0];
      chars++;
    }
  }

  return ret;
}


string translate(rostring origSrc, rostring srcchars, rostring destchars)
{
  // first, expand range notation in the specification sequences
  string srcSpec = expandRanges(toCStr(srcchars));
  string destSpec = expandRanges(toCStr(destchars));

  // build a translation map
  char map[256];
  int i;
  for (i=0; i<256; i++) {
    map[i] = i;
  }

  // excess characters from either string are ignored ("SysV" behavior)
  for (i=0; i < srcSpec.length() && i < destSpec.length(); i++) {
    map[(unsigned char)( srcSpec[i] )] = destSpec[i];
  }

  // run through 'src', applying 'map'
  char const *src = toCStr(origSrc);
  Array<char> ret(strlen(src)+1);
  char *dest = ret.ptr();
  while (*src) {
    *dest = map[(unsigned char)*src];
    dest++;
    src++;
  }
  *dest = 0;    // final nul terminator

  return string(ret);
}


// why is this necessary?
string stringToupper(rostring src)
  { return translate(src, "a-z", "A-Z"); }


string trimWhitespace(rostring origStr)
{                                   
  char const *str = toCStr(origStr);

  // trim leading whitespace
  while (isspace(*str)) {
    str++;
  }

  // trim trailing whitespace
  char const *end = str + strlen(str);
  while (end > str &&
         isspace(end[-1])) {
    end--;
  }

  // return it
  return substring(str, end-str);
}


string firstAlphanumToken(rostring origStr)
{                                   
  char const *str = toCStr(origStr);

  // find the first alpha-numeric; NOTE: if we hit the NUL at the end,
  // that should not be alpha-numeric and we should stop
  while(!isalnum(*str)) {
    str++;
  }

  // keep going until we are not at an alpha-numeric
  char const *end = str;
  while(isalnum(*end)) {
    end++;
  }

  // return it
  return substring(str, end-str);
}


// table of escape codes
static struct Escape {
  char actual;      // actual character in string
  char escape;      // char that follows backslash to produce 'actual'
} const escapes[] = {
  { '\0', '0' },  // nul
  { '\a', 'a' },  // bell
  { '\b', 'b' },  // backspace
  { '\f', 'f' },  // form feed
  { '\n', 'n' },  // newline
  { '\r', 'r' },  // carriage return
  { '\t', 't' },  // tab
  { '\v', 'v' },  // vertical tab
  { '\\', '\\'},  // backslash
  { '"',  '"' },  // double-quote
  { '\'', '\''},  // single-quote
};


string encodeWithEscapes(char const *p, int len)
{
  stringBuilder sb;

  for (; len>0; len--, p++) {
    // look for an escape code
    unsigned i;
    for (i=0; i<TABLESIZE(escapes); i++) {
      if (escapes[i].actual == *p) {
        sb << '\\' << escapes[i].escape;
        break;
      }
    }
    if (i<TABLESIZE(escapes)) {
      continue;   // found it and printed it
    }

    // try itself
    if (isprint(*p)) {
      sb << *p;
      continue;
    }

    // use the most general notation
    char tmp[5];
    sprintf(tmp, "\\x%02X", (unsigned char)(*p));
    sb << tmp;
  }
  
  return sb;
}


string encodeWithEscapes(rostring p)
{
  return encodeWithEscapes(toCStr(p), strlen(p));
}


string quoted(rostring src)
{
  return stringc << "\""
                 << encodeWithEscapes(src)
                 << "\"";
}


void decodeEscapes(ArrayStack<char> &dest, rostring origSrc,
                   char delim, bool allowNewlines)
{
  char const *src = toCStr(origSrc);

  while (*src != '\0') {
    if (*src == '\n' && !allowNewlines) {
      xformat("unescaped newline (unterminated string)");
    }
    if (*src == delim) {
      xformat(stringc << "unescaped delimiter (" << delim << ")");
    }

    if (*src != '\\') {
      // easy case
      dest.push(*src);
      src++;
      continue;
    }

    // advance past backslash
    src++;

    // see if it's a simple one-char backslash code;
    // start at 1 so we do *not* use the '\0' code since
    // that's actually a special case of \0123', and
    // interferes with the latter
    int i;
    for (i=1; i<TABLESIZE(escapes); i++) {
      if (escapes[i].escape == *src) {
        dest.push(escapes[i].actual);
        src++;
        break;
      }
    }
    if (i < TABLESIZE(escapes)) {
      continue;
    }

    if (*src == '\0') {
      xformat("backslash at end of string");
    }

    if (*src == '\n') {
      // escaped newline; advance to first non-whitespace
      src++;
      while (*src==' ' || *src=='\t') {
        src++;
      }
      continue;
    }

    if (*src == 'x' || isdigit(*src)) {
      // hexadecimal or octal char (it's unclear to me exactly how to
      // parse these since it's supposedly legal to have e.g. "\x1234"
      // mean a one-char string.. whatever)
      bool hex = (*src == 'x');
      if (hex) {
        src++;

        // strtoul is willing to skip leading whitespace, so I need
        // to catch it myself
        if (isspace(*src)) {
          xformat("whitespace following hex (\\x) escape");
        }
      }

      char const *endptr;
      unsigned long val = strtoul(src, (char**)&endptr, hex? 16 : 8);
      if (src == endptr) {
        // this can't happen with the octal escapes because
        // there is always at least one valid digit
        xformat("invalid hex (\\x) escape");
      }

      dest.push((char)(unsigned char)val);    // possible truncation..
      src = endptr;
      continue;
    }

    // everything not explicitly covered will be considered
    // an error (for now), even though the C++ spec says
    // it should be treated as if the backslash were not there
    //
    // 7/29/04: now making backslash the identity transformation in
    // this case
    //
    // copy character as if it had not been backslashed
    dest.push(*src);
    src++;
  }
}


string parseQuotedString(rostring text)
{
  if (!( text[0] == '"' &&
         text[strlen(text)-1] == '"' )) {
    xformat(stringc << "quoted string is missing quotes: " << text);
  }

  // strip the quotes
  string noQuotes = substring(toCStr(text)+1, strlen(text)-2);

  // decode escapes
  ArrayStack<char> buf;
  decodeEscapes(buf, noQuotes, '"');
  buf.push(0 /*NUL*/);

  // return string contents up to first NUL, which isn't necessarily
  // the same as the one just pushed; by invoking this function, the
  // caller is accepting responsibility for this condition
  return string(buf.getArray());
}


string localTimeString()
{
  time_t t = time(NULL);
  char const *p = asctime(localtime(&t));
  return substring(p, strlen(p) - 1);     // strip final newline
}


string sm_basename(rostring origSrc)
{
  char const *src = toCStr(origSrc);

  char const *sl = strrchr(src, '/');   // locate last slash
  if (sl && sl[1] == 0) {
    // there is a slash, but it is the last character; ignore it
    // (this behavior is what /bin/basename does)
    return sm_basename(substring(src, strlen(src)-1));
  }

  if (sl) {
    return string(sl+1);     // everything after the slash
  }
  else {
    return string(src);      // entire string if no slashes
  }
}

string dirname(rostring origSrc)
{                              
  char const *src = toCStr(origSrc);

  char const *sl = strrchr(src, '/');   // locate last slash
  if (sl == src) {
    // last slash is leading slash
    return string("/");
  }

  if (sl && sl[1] == 0) {
    // there is a slash, but it is the last character; ignore it
    // (this behavior is what /bin/dirname does)
    return dirname(substring(src, strlen(src)-1));
  }

  if (sl) {
    return substring(src, sl-src);     // everything before slash
  }
  else {
    return string(".");
  }
}


// I will expand this definition to use more knowledge about English
// irregularities as I need it
string plural(int n, rostring prefix)
{
  if (n==1) {
    return prefix;
  }

  if (0==strcmp(prefix, "was")) {
    return string("were");
  }
  if (prefix[strlen(prefix)-1] == 'y') {
    return stringc << substring(prefix, strlen(prefix)-1) << "ies";
  }
  else {
    return stringc << prefix << "s";
  }
}

string pluraln(int n, rostring prefix)
{
  return stringc << n << " " << plural(n, prefix);
}


string a_or_an(rostring noun)
{
  bool use_an = false;

  if (strchr("aeiouAEIOU", noun[0])) {
    use_an = true;
  }

  // special case: I pronounce "mvisitor" like "em-visitor"
  if (noun[0]=='m' && noun[1]=='v') {
    use_an = true;
  }
  
  if (use_an) {
    return stringc << "an " << noun;
  }
  else {
    return stringc << "a " << noun;
  }
}


char *copyToStaticBuffer(char const *s)
{           
  enum { SZ=200 };
  static char buf[SZ+1];

  int len = strlen(s);
  if (len > SZ) len=SZ;
  memcpy(buf, s, len);
  buf[len] = 0;

  return buf;
}


bool prefixEquals(rostring str, rostring prefix)
{
  int slen = strlen(str);
  int plen = strlen(prefix);
  return slen >= plen &&
         0==memcmp(toCStr(str), toCStr(prefix), plen);
}

bool suffixEquals(rostring str, rostring suffix)
{
  int slen = strlen(str);
  int ulen = strlen(suffix);    // sUffix
  return slen >= ulen &&
         0==memcmp(toCStr(str)+slen-ulen, toCStr(suffix), ulen);
}


void writeStringToFile(rostring str, rostring fname)
{
  AutoFILE fp(toCStr(fname), "w");

  if (fputs(toCStr(str), fp) < 0) {
    xbase("fputs: EOF");
  }
}


string readStringFromFile(rostring fname)
{
  AutoFILE fp(toCStr(fname), "r");

  stringBuilder sb;

  char buf[4096];
  for (;;) {
    int len = fread(buf, 1, 4096, fp);
    if (len < 0) {
      xbase("fread failed");
    }
    if (len == 0) {
      break;
    }

    sb.append(buf, len);
  }

  return sb;
}


bool readLine(string &dest, FILE *fp)
{
  char buf[80];

  if (!fgets(buf, 80, fp)) {
    return false;
  }

  if (buf[strlen(buf)-1] == '\n') {
    // read a newline, we got the whole line
    dest = buf;
    return true;
  }

  // only got part of the string; need to iteratively construct
  stringBuilder sb;
  while (buf[strlen(buf)-1] != '\n') {
    sb << buf;
    if (!fgets(buf, 80, fp)) {
      // found eof after partial; return partial *without* eof
      // indication, since we did in fact read something
      break;
    }
  }

  dest = sb;
  return true;
}


string chomp(rostring src)
{
  if (!src.empty() && src[strlen(src)-1] == '\n') {
    return substring(src, strlen(src)-1);
  }
  else {
    return src;
  }
}


// ----------------------- test code -----------------------------
#ifdef TEST_STRUTIL

#include "test.h"      // USUAL_MAIN
#include <stdio.h>     // printf

void expRangeVector(char const *in, char const *out)
{
  printf("expRangeVector(%s, %s)\n", in, out);
  string result = expandRanges(in);
  xassert(result.equals(out));
}

void trVector(char const *in, char const *srcSpec, char const *destSpec, char const *out)
{
  printf("trVector(%s, %s, %s, %s)\n", in, srcSpec, destSpec, out);
  string result = translate(in, srcSpec, destSpec);
  xassert(result.equals(out));
}

void decodeVector(char const *in, char const *out, int outLen)
{
  printf("decodeVector: \"%s\"\n", in);
  ArrayStack<char> dest;
  decodeEscapes(dest, in, '\0' /*delim, ignored*/, false /*allowNewlines*/);
  xassert(dest.length() == outLen);
  xassert(0==memcmp(out, dest.getArray(), dest.length()));
}

void basenameVector(char const *in, char const *out)
{
  printf("basenameVector(%s, %s)\n", in, out);
  string result = sm_basename(in);
  xassert(result.equals(out));
}

void dirnameVector(char const *in, char const *out)
{
  printf("dirnameVector(%s, %s)\n", in, out);
  string result = dirname(in);
  xassert(result.equals(out));
}

void pluralVector(int n, char const *in, char const *out)
{
  printf("pluralVector(%d, %s, %s)\n", n, in, out);
  string result = plural(n, in);
  xassert(result.equals(out));
}


void entry()
{
  expRangeVector("abcd", "abcd");
  expRangeVector("a", "a");
  expRangeVector("a-k", "abcdefghijk");
  expRangeVector("0-9E-Qz", "0123456789EFGHIJKLMNOPQz");

  trVector("foo", "a-z", "A-Z", "FOO");
  trVector("foo BaR", "a-z", "A-Z", "FOO BAR");
  trVector("foo BaR", "m-z", "M-Z", "fOO BaR");

  decodeVector("\\r\\n", "\r\n", 2);
  decodeVector("abc\\0def", "abc\0def", 7);
  decodeVector("\\033", "\033", 1);
  decodeVector("\\x33", "\x33", 1);
  decodeVector("\\?", "?", 1);

  basenameVector("a/b/c", "c");
  basenameVector("abc", "abc");
  basenameVector("/", "");
  basenameVector("a/b/c/", "c");

  dirnameVector("a/b/c", "a/b");
  dirnameVector("a/b/c/", "a/b");
  dirnameVector("/a", "/");
  dirnameVector("abc", ".");
  dirnameVector("/", "/");

  pluralVector(1, "path", "path");
  pluralVector(2, "path", "paths");
  pluralVector(1, "fly", "fly");
  pluralVector(2, "fly", "flies");
  pluralVector(2, "was", "were");
}


USUAL_MAIN

#endif // TEST_STRUTIL
