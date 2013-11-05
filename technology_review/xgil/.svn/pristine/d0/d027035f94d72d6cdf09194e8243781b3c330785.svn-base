#include "xmlhelp.h"            // this module
#include <stdlib.h>             // atof, atol

string toXml_bool(bool b) {
  if (b) return "true";
  else return "false";
}

void fromXml_bool(bool &b, rostring str) {
  b = streq(str, "true");
}


string toXml_int(int i) {
  return stringc << i;
}

void fromXml_int(int &i, rostring str) {
  long i0 = strtol(str.c_str(), NULL, 10);
  i = i0;
}


string toXml_long(long i) {
  return stringc << i;
}

void fromXml_long(long &i, rostring str) {
  long i0 = strtol(str.c_str(), NULL, 10);
  i = i0;
}


string toXml_unsigned_int(unsigned int i) {
  return stringc << i;
}

void fromXml_unsigned_int(unsigned int &i, rostring str) {
  unsigned long i0 = strtoul(str.c_str(), NULL, 10);
  i = i0;
}


string toXml_unsigned_long(unsigned long i) {
  return stringc << i;
}

void fromXml_unsigned_long(unsigned long &i, rostring str) {
  unsigned long i0 = strtoul(str.c_str(), NULL, 10);
  i = i0;
}


string toXml_double(double x) {
  return stringc << x;
}

void fromXml_double(double &x, rostring str) {
  x = atof(str.c_str());
}


string toXml_SourceLoc(SourceLoc loc) {
  return sourceLocManager->getString(loc);
}

void fromXml_SourceLoc(SourceLoc &loc, rostring str) {
  xfailure("not implemented");
}
