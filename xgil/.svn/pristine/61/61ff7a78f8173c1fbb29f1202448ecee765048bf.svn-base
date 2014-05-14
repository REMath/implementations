// asthelp.cc            see license.txt for copyright and terms of use
// code for what's declared in asthelp.h

#include "asthelp.h"       // this module
#include "strutil.h"       // quoted

// ----------- debugPrint helpers -----------------------
ostream &ind(ostream &os, int indent)
{
  while (indent--) {
    os << " ";
  }
  return os;
}


void debugPrintStr(string const &s, char const *name,
                   ostream &os, int indent)
{
  debugPrintStr(s.c_str(), name, os, indent);
}

void debugPrintStr(char const *s, char const *name,
                   ostream &os, int indent)
{
  string s1((s) ? string(s) : string("NULL"));
  ind(os, indent) << name << " = " << quoted(s1) << "\n";
}


void debugPrintCStr(char const *s, char const *name,
                    ostream &os, int indent)
{
  ind(os, indent) << name << " = ";
  if (s) {
    os << quoted(s);
  }
  else {
    os << "(null)";
  }
  os << "\n";
}


template <class STR>
void debugPrintStringList(ASTList<STR> const &list, char const *name,
                          ostream &os, int indent)
{
  ind(os, indent) << name << ": ";
  {
    int ct=0;
    FOREACH_ASTLIST(STR, list, iter) {
      if (ct++ > 0) {
        os << ", ";
      }
      os << quoted(string(*( iter.data() )));
    }
  }
  os << "\n";
}


void debugPrintList(ASTList<string> const &list, char const *name,
                    ostream &os, int indent)
{
  debugPrintStringList(list, name, os, indent);
}

void debugPrintList(ASTList<LocString> const &list, char const *name,
                    ostream &os, int indent)
{
  debugPrintStringList(list, name, os, indent);
}


// ----------- xmlPrint helpers -----------------------
void xmlPrintStr(string const &s, char const *name,
                 ostream &os, int indent)
{
  ind(os, indent) << "<member type=string name = \"" << name << "\">\n";
  // dsw: quoted might add another layer of quotes.
  ind(os, indent+2) << "<value type=string val=\"" << quoted(s) << "\" />\n";
  ind(os, indent) << "</member>\n";
}


template <class STR>
void xmlPrintStringList(ASTList<STR> const &list, char const *name,
                        ostream &os, int indent)
{
  ind(os, indent) << "<member type=stringList name = \"" << name << "\">\n";
  {
    FOREACH_ASTLIST(STR, list, iter) {
      // dsw: quoted might add another layer of quotes.
      ind(os, indent+2) << "<object type=string val=\"" 
                        << quoted(string(*( iter.data() ))) << "\" />\n";
    }
  }
  ind(os, indent) << "</member>\n";
}


void xmlPrintList(ASTList<string> const &list, char const *name,
                  ostream &os, int indent)
{
  xmlPrintStringList(list, name, os, indent);
}

void xmlPrintList(ASTList<LocString> const &list, char const *name,
                  ostream &os, int indent)
{
  xmlPrintStringList(list, name, os, indent);
}


void xmlPrintPointer(ostream &os, char const *label, void const *p)
{
  if (!p) {
    // sm: previously, the code for this function just inserted 'p'
    // as a 'void const *', but that is nonportable, as gcc-3 inserts
    // "0" while gcc-2 emits "(nil)"
    os << label << "0";
  }
  else {
    // sm: I question whether this is portable, but it may not matter
    // since null pointers are the only ones that are treated
    // specially (as far as I can tell)
    os << label << p;
  }
}


// EOF
