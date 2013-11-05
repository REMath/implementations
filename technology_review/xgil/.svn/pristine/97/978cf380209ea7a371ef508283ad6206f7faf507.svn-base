// xassert.h            see license.txt for copyright and terms of use
// Scott McPeak, 1997-1998  This file is public domain.

#ifndef XASSERT_H
#define XASSERT_H

#include "macros.h"     // NORETURN

// bhackett: replaced assert exception with Xgill asserts.

// include Xgill alloc.h file overriding operator new/delete globally.
// if anything under Elsa calls new/delete and does not transitively
// include this file, things will probably break. however, this is the
// simplest and seemingly most portable solution for precisely tracking
// how much memory has been heap-allocated by the process.
#include "../../util/alloc.h"

// use Xgill asserts.
#include "../../util/assert.h"

// Ordinary 'xassert' *can* be turned off, but the nominal intent
// is that it be left on, under the "ship what you test" theory.
// I advocate using NDEBUG_NO_ASSERTIONS only as a way to gauge the
// performance impact of the existing assertions.
#if !defined(NDEBUG_NO_ASSERTIONS)
  #define xassert(cond) Assert(cond)
#else
  #define xassert(cond) do { } while (0)
#endif

// Here's a version which will turn off with ordinary NDEBUG.  It
// is for more expensive checks that need not ship.
#if !defined(NDEBUG)
  #define xassertdb(cond) xassert(cond)
#else
  #define xassertdb(cond) do { } while (0)
#endif

// call when state is known to be bad; will *not* return
#define xfailure(why) xassert(0)

#endif // XASSERT_H

