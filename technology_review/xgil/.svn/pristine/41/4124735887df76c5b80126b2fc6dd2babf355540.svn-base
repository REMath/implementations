// exc.h            see license.txt for copyright and terms of use
// exception classes for SafeTP project
// Scott McPeak, 1996-1998  This file is public domain.

// I apologize for the inconsistent naming in this module.  It is
// the product of an extended period of experimenting with naming
// conventions for exception-related concepts.  The names near the
// end of the file reflect my current preferences.

#ifndef EXC_H
#define EXC_H

#include "breaker.h"     // breaker
#include "typ.h"         // bool
#include "xassert.h"     // xassert, for convenience for #includers
#include "str.h"         // string

// forward declarations
class stringBuilder;


// by using this macro, the debugger gets a shot before the stack is unwound
#ifdef THROW
#undef THROW
#endif
#define THROW(obj) \
  { throw (obj); }


// My intention is to put a call to this macro at the beginning of
// every catch block.  Its (default) definition is to call breaker so
// that in the debugger I can easily get to the point where an
// exception is caught.
#define HANDLER() /* user ; */


// this function returns true if we're in the process of unwinding the
// stack, and therefore destructors may want to avoid throwing new exceptions;
// for now, may return false positives, but won't return false negatives
bool unwinding();

// inside a catch expression, the unwinding() function needs a tweak; pass
// the caught expression, and this returns whether there any *additional*
// exceptions currently in flight
class xBase;
bool unwinding_other(xBase const &x);

// using unwinding() in destructors to avoid abort()
#define CAUTIOUS_RELAY           \
  catch (xBase &x) {             \
    if (!unwinding_other(x)) {   \
      throw;   /* re-throw */    \
    }                            \
  }


// -------------------- xBase ------------------
// intent is to derive all exception objects from this
class xBase {
protected:
  // the human-readable description of the exception
  string msg;

public:
  // initially true; when true, we write a record of the thrown exception
  // to clog
  static bool logExceptions;

  // current # of xBases running about; used to support unrolling()
  static int creationCount;

public:
  xBase(rostring m);       // create exception object with message 'm'
  xBase(xBase const &m);   // copy ctor
  virtual ~xBase();

  rostring why() const
    { return msg; }

  // print why
  void insert(ostream &os) const;
  friend ostream& operator << (ostream &os, xBase const &obj)
    { obj.insert(os); return os; }

  // add a string describing what was going on at the time the
  // exception was thrown; this should be called with the innermost
  // context string first, i.e., in the normal unwind order
  void addContext(rostring context);
};

// equivalent to THROW(xBase(msg))
void xbase(rostring msg) NORETURN;


// ---------------------- xFormat -------------------
// throwing this means a formatting error has been detected
// in some input data; the program cannot process it, but it
// is not a bug in the program
class xFormat : public xBase {
  string condition;          // what is wrong with the input

public:
  xFormat(rostring cond);
  xFormat(xFormat const &obj);
  ~xFormat();

  rostring cond() const { return condition; }
};

// compact way to throw an xFormat
void xformat(rostring condition) NORETURN;

// convenient combination of condition and human-readable message
#define checkFormat(cond, message) \
  ((cond)? (void)0 : xformat(message))

// assert-like interface to xFormat
void formatAssert_fail(char const *cond, char const *file, int line) NORETURN;

#define formatAssert(cond) \
  ((cond)? (void)0 : formatAssert_fail(#cond, __FILE__, __LINE__))

  
// -------------------- XOpen ---------------------
// thrown when we fail to open a file
class XOpen : public xBase {
public:
  string filename;
  
public:
  XOpen(rostring fname);
  XOpen(XOpen const &obj);
  ~XOpen();
};

void throw_XOpen(rostring fname) NORETURN;


// -------------------- XOpenEx ---------------------
// more informative
class XOpenEx : public XOpen {
public:
  string mode;         // fopen-style mode string, e.g. "r"
  string cause;        // errno-derived failure cause, e.g. "no such file"

public:
  XOpenEx(rostring fname, rostring mode, rostring cause);
  XOpenEx(XOpenEx const &obj);
  ~XOpenEx();
                                              
  // convert a mode string as into human-readable participle,
  // e.g. "r" becomes "reading"
  static string interpretMode(rostring mode);
};

void throw_XOpenEx(rostring fname, rostring mode, rostring cause) NORETURN;


// ------------------- XUnimp ---------------------
// thrown in response to a condition that is in principle
// allowed but not yet handled by the existing code
class XUnimp : public xBase {
public:
  XUnimp(rostring msg);
  XUnimp(XUnimp const &obj);
  ~XUnimp();
};

void throw_XUnimp(rostring msg) NORETURN;

// throw XUnimp with file/line info
void throw_XUnimp(char const *msg, char const *file, int line) NORETURN;

#define xunimp(msg) throw_XUnimp(msg, __FILE__, __LINE__)


// ------------------- XFatal ---------------------
// thrown in response to a user action that leads to an unrecoverable
// error; it is not due to a bug in the program
class XFatal : public xBase {
public:
  XFatal(rostring msg);
  XFatal(XFatal const &obj);
  ~XFatal();
};

void throw_XFatal(rostring msg) NORETURN;
#define xfatal(msg) throw_XFatal(stringc << msg)


#endif // EXC_H

