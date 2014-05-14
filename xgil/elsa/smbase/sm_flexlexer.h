// sm_flexlexer.h
// a layer of indirection to try to work with different
// installed versions of Flex


// Basically, what has happened is the last version of flex created by
// Vern Paxson et al. is 2.5.4, and a lot of distributions use that.
// More recently some other people started a project hosted at
// Sourceforge, and their current (only?) release is flex-2.5.31.
// Unfortunately, the authors of 2.5.31 do not appear concerned with
// maintaining compatibility for C++ scanners.
//
// See bug "[ 751550 ] c++ derived scanners will not compile",
// http://sourceforge.net/tracker/index.php?func=detail&aid=751550&group_id=72099&atid=533377
//
// So in an attempt to make Elkhound/Elsa work, this file is where
// I'll put my hacks.


// workaround for flex-2.5.31 bug
#ifdef yyFlexLexer
  #undef yyFlexLexer
#endif

// pull in stream classes
#include "xassert.h"

// now get the installed FlexLexer.h.. this nominally lives in
// /usr/include or /usr/local/include, depending on how Flex is
// installed
#include "../flex/FlexLexer.h"
