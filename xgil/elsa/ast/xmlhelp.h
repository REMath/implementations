// xmlhelp.h            see license.txt for copyright and terms of use
// included by generated ast code

// Generic serialization and de-serialization support.

#ifndef XMLHELP_H
#define XMLHELP_H

#include "str.h"         // string
#include "srcloc.h"      // SourceLoc

// I have manually mangled the name to include "_bool" or "_int" as
// otherwise what happens is that if a toXml() for some enum flag is
// missing then the C++ compiler will just use the toXml(bool)
// instead, which is a bug.
string toXml_bool(bool b);
void fromXml_bool(bool &b, rostring str);

string toXml_int(int i);
void fromXml_int(int &i, rostring str);

string toXml_long(long i);
void fromXml_long(long &i, rostring str);

string toXml_unsigned_int(unsigned int i);
void fromXml_unsigned_int(unsigned int &i, rostring str);

string toXml_unsigned_long(unsigned long i);
void fromXml_unsigned_long(unsigned long &i, rostring str);

string toXml_double(double x);
void fromXml_double(double &x, rostring str);

string toXml_SourceLoc(SourceLoc loc);
void fromXml_SourceLoc(SourceLoc &loc, rostring str);

#endif // XMLHELP_H
