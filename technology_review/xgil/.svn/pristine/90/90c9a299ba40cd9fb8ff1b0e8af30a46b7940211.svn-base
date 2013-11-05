// strutil.h            see license.txt for copyright and terms of use
// various string utilities built upon the 'str' module
// Scott McPeak, July 2000

#ifndef STRUTIL_H
#define STRUTIL_H

#include "str.h"      // string
#include "array.h"    // ArrayStack

#include <stdio.h>    // FILE


// direct string replacement, replacing instances of oldstr with newstr
// (newstr may be "")
string replace(rostring src, rostring oldstr, rostring newstr);

// works like unix "tr": the source string is translated character-by-character,
// with occurrences of 'srcchars' replaced by corresponding characters from
// 'destchars'; further, either set may use the "X-Y" notation to denote a
// range of characters from X to Y
string translate(rostring src, rostring srcchars, rostring destchars);

// a simple example of using translate; it was originally inline, but a bug
// in egcs made me move it out of line
string stringToupper(rostring src);
//  { return translate(src, "a-z", "A-Z"); }


// remove any whitespace at the beginning or end of the string
string trimWhitespace(rostring str);
// dsw: get the first alphanum token in the string
string firstAlphanumToken(rostring str);


// encode a block of bytes as a string with C backslash escape
// sequences (but without the opening or closing quotes)
//
// 'src' is *not* rostring, since it is not NUL terminated
string encodeWithEscapes(char const *src, int len);

// safe when the text has no NUL characters
string encodeWithEscapes(rostring src);

// adds the quotes too
string quoted(rostring src);


// decode an escaped string; throw xFormat if there is a problem
// with the escape syntax; if 'delim' is specified, it will also
// make sure there are no unescaped instances of that
void decodeEscapes(ArrayStack<char> &dest, rostring src,
                   char delim = 0, bool allowNewlines=false);

// given a string with quotes and escapes, yield just the string;
// works if there are no escaped NULs
string parseQuotedString(rostring text);


// this probably belongs in a dedicated module for time/date stuff..
// returns asctime(localtime(time))
string localTimeString();


// given a directory name like "a/b/c", return "c"
// renamed from 'basename' because of conflict with something in string.h
string sm_basename(rostring src);

// given a directory name like "a/b/c", return "a/b"; if 'src' contains
// no slashes at all, return "."
string dirname(rostring src);


// return 'prefix', pluralized if n!=1; for example
//   plural(1, "egg") yields "egg", but
//   plural(2, "egg") yields "eggs";
// it knows about a few irregular pluralizations (see the source),
// and the expectation is I'll add more irregularities as I need them
string plural(int n, rostring prefix);

// same as 'plural', but with the stringized version of the number:
//   pluraln(1, "egg") yields "1 egg", and
//   pluraln(2, "egg") yields "2 eggs"
string pluraln(int n, rostring prefix);

// prepend with an indefinite article:
//   a_or_an("foo") yields "a foo", and
//   a_or_an("ogg") yields "an ogg"
string a_or_an(rostring noun);


// Sometimes it's useful to store a string value in a static buffer;
// most often this is so 'gdb' can see the result.  This function just
// copies its input into a static buffer (of unspecified length, but
// it checks bounds internally), and returns a pointer to that buffer.
char *copyToStaticBuffer(char const *src);


// true if the first part of 'str' matches 'prefix'
bool prefixEquals(rostring str, rostring prefix);

// and similar for last part
bool suffixEquals(rostring str, rostring suffix);


// read/write strings <-> files
void writeStringToFile(rostring str, rostring fname);
string readStringFromFile(rostring fname);


// read the next line from a FILE* (e.g. an AutoFILE); the
// newline is returned if it is present (you can use 'chomp'
// to remove it); returns false (and "") on EOF
bool readLine(string &dest, FILE *fp);


// like perl 'chomp': remove a final newline if there is one
string chomp(rostring src);


#endif // STRUTIL_H
