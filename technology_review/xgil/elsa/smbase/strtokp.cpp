// strtokp.cc            see license.txt for copyright and terms of use
// code for strtokp.h
// Scott McPeak, 1997, 1999, 2000  This file is public domain.

#include "strtokp.h"    // this module
#include "exc.h"        // xassert
#include <string.h>     // strtok


StrtokParse::StrtokParse(rostring origStr, rostring origDelim)
  : buf(strlen(origStr)+1)
{
  char const *str = toCStr(origStr);
  char const *delim = toCStr(origDelim);

  // make local copy
  strcpy(buf, str);

  // parse it first time to count # of tokens
  int ct=0;
  char *tok = strtok(buf.ptr(), delim);
  while (tok) {
    ct++;
    tok = strtok(NULL, delim);
  }

  // restore buf
  strcpy(buf, str);

  // allocate storage
  _tokc = ct;
  if (ct) {
    _tokv = new char*[ct+1];
    _tokv[ct] = NULL;     // terminate argv[]-like list
  }
  else {
    _tokv = NULL;
  }

  // parse it again, this time saving the values
  ct=0;
  tok = strtok(buf.ptr(), delim);
  while (tok) {
    _tokv[ct] = tok;
    ct++;
    tok = strtok(NULL, delim);
  }

  // simple check just because it's easy
  xassert(ct == _tokc);
}


StrtokParse::~StrtokParse()
{
  // buf deletes itself

  if (_tokv) {
    delete[] _tokv;
  }
}


void StrtokParse::validate(int which) const
{
  xassert((unsigned)which < (unsigned)_tokc);
}


char const *StrtokParse::tokv(int which) const
{
  validate(which);
  return _tokv[which];
}


string StrtokParse::
  reassemble(int firstTok, int lastTok, rostring original) const
{
  int left = offset(firstTok);
  int right = offset(lastTok) + strlen(tokv(lastTok));

  return substring(toCStr(original) + left, right-left);
}


string StrtokParse::
  join(int firstTok, int lastTok, rostring separator) const
{
  stringBuilder sb;
  
  for (int i=firstTok; i<=lastTok; i++) {
    if (i > firstTok) {
      sb << separator;
    }
    sb << tokv(i);
  }
  
  return sb;
}


int StrtokParse::offset(int which) const
{
  return tokv(which) - (char const*)buf;
}
