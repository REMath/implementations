#include "stubs.h"

/* Note on NEEDLE_SZ: The original program searches for "+CMGR:" or
 * "+CMGL: ", and then skips seven characters in either case. I
 * *think* that they meant to have a space after teh "+CMGR:", but
 * just forgot it, and the parsing works right either way. 
 */
#define NEEDLE "+C" // "+CMGR:" or "+CMGL: "
#define NEEDLE_SZ 2 // 7 

#define NEEDLE2 "," // ",,0\r"

#define MIN_DIFF 256

/* fetchsms() aborts if it can't advance end at least MIN_DIFF
 * characters twice; so, make PDUSIZE 2*MIN_DIFF.
 */
#define PDUSIZE 2*MIN_DIFF

/* NEEDLE_SZ  -- because we search for NEEDLE and skip it
 *
 * PDUSIZE + 2 so we have enough left to overflow pdu[]
 */
#define ANSWERSIZE NEEDLE_SZ + PDUSIZE + 2

