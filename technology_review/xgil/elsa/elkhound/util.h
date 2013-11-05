// util.h            see license.txt for copyright and terms of use
// collection of utility macros and functions that are
// candidates for adding to the smbase library

#ifndef __UTIL_H
#define __UTIL_H

#include "trace.h"     // trace

// given a method called 'print', define an operator to use it
#define OSTREAM_OPERATOR(MyClass)                                \
  friend ostream &operator << (ostream &os, MyClass const &ths)  \
    { ths.print(os); return os; }


// I'm experimenting with the idea of making my control structures
// more declarative
#define INTLOOP(var, start, maxPlusOne) \
  for (int var = start; var < maxPlusOne; var++)


// experiment: given (a reference to), an owner pointer, yield the pointer
// value after nullifying the given pointer
template <class T>
inline T *transferOwnership(T *&ptr)
{
  T *ret = ptr;
  ptr = NULL;
  return ret;
}


// print a value under the debug trace (name: Trace VALue)
#define TVAL(expr) \
  trace("debug") << #expr ": " << (expr) << endl


#endif // __UTIL_H
