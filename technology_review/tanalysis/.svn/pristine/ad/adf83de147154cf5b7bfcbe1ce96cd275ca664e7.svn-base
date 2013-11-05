#include "stubs.h"

/* Size of buffer being overflowed, and most input buffers. We
 * strncmp() it against "../", so make sure it has at least 3
 * cells. */
#define MAXPATHLEN 256

typedef int size_t;
typedef short uid_t;
uid_t geteuid(void);
int seteuid(uid_t euid);

int     enable_signaling();
int     delay_signaling();

int readlink(const char *path, char *buf, int bufsiz);
char *getcwd(char *buf, size_t size);
