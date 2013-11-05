#include "constants.h"

#ifndef BOOL
typedef int BOOL;
#endif

struct winbindd_request {
  union {
    /* Got rid of most union fields.... */
    fstring winsreq;     /* WINS request */
    BOOL list_all_domains;
  } data;
};

union nss_XbyY_key {
  /* Got rid of most fields.... */
  const char *name;
  int number;
};

typedef struct nss_XbyY_args {
  union nss_XbyY_key key;
} nss_XbyY_args_t;

