#ifndef CONSTANTS_C
#define CONSTANTS_C

#include "stubs.h"

/* Originally "-rwxdls". This will affect the number of times strchr()
 * loops, so vary it to vary analysis difficulty. */
#define CHARS_NOT_WANTED "-"

/* Size of the buffer being overflowed */
#define USERSZ 256

/* One less than the number of iterations the first FOR loop must go
 * through in order to hit the error. 
 *
 * XXX Not sure how this affects analysis difficulty, except that the
 * XXX bigger this is, the bigger INSZ has to be.*/
#define J 2

/* Must read at least NPFLEN characters and contain the string NPF in
 * order to cal ftpls(). */
#define NPF "N"
#define NPFSZ 1

/* Size of the input buffer. Also affects a loop bound. */
#define INSZ USERSZ + NPFSZ + J + 2

#endif
