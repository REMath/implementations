// asockind.cc            see license.txt for copyright and terms of use
// code for asockind.h

#include "asockind.h"    // this module
#include "xassert.h"     // xassert

string toString(AssocKind k)
{
  static char const * const arr[] = {
    "AK_LEFT", 
    "AK_RIGHT", 
    "AK_NONASSOC", 
    "AK_NEVERASSOC", 
    "AK_SPLIT"
  };
  STATIC_ASSERT(TABLESIZE(arr) == NUM_ASSOC_KINDS);
  xassert((unsigned)k < NUM_ASSOC_KINDS);
  return string(arr[k]);
}
