// autofile.cc            see license.txt for copyright and terms of use
// code for autofile.h

#include "autofile.h"     // this module
#include "exc.h"          // throw_XOpen

#include <errno.h>        // errno
#include <string.h>       // strerror


FILE *xfopen(char const *fname, char const *mode)
{
  FILE *ret = fopen(fname, mode);
  if (!ret) {
    throw_XOpenEx(fname, mode, strerror(errno));
  }

  return ret;
}


AutoFILE::AutoFILE(char const *fname, char const *mode)
  : AutoFclose(xfopen(fname, mode))
{}

AutoFILE::~AutoFILE()
{
  // ~AutoFclose closes the file
}


// -------------------- test code -------------------
// really this code is to test XOpenEx and strerror
#ifdef TEST_AUTOFILE

#include "test.h"         // ARGS_MAIN

void entry(int argc, char *argv[])
{                         
  if (argc < 2) {
    cout << "usage: " << argv[0] << " filename [mode]\n";
    return;
  }

  char const *mode = "r";
  if (argc >= 3) {
    mode = argv[2];
  }

  cout << "about to open " << argv[1] << " with mode " << mode << endl;

  {
    AutoFILE fp(argv[1], mode);
    cout << argv[1] << " is now open" << endl;
  }

  cout << argv[1] << " is now closed" << endl;
}

ARGS_MAIN


#endif // TEST_AUTOFILE
