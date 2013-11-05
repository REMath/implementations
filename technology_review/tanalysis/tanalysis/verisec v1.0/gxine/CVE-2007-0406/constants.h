#include "stubs.h"

/* Size of buffer being overflowed. 
 * Ensure that SUN_PATH_SZ - 1 is non-negative */
#define SUN_PATH_SZ 256 + 1/* originally 108 */

/* Size of input buffer. */
#define FILENAME_SZ SUN_PATH_SZ + 2  /* originally 1024 */

struct sockaddr_un
{
  char sun_path[SUN_PATH_SZ];         /* Path name.  */
};
