
#include "../sixgill.h"

// annotation issues with namespaces.

namespace named {
  typedef int Whatever;
}

using namespace named;

postcondition(return == sizeof(Whatever))
int foo()
{
  return 4;
}
