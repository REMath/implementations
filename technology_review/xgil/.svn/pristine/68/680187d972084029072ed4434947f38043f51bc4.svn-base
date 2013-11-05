
#include "../sixgill.h"

// annotation issues on templates.

template <typename TEMPLATE>
struct templateStruct
{
  typedef TEMPLATE ThisType;
  static int SizeOfType() { return sizeof(TEMPLATE); }

  //invariant(field == SizeOfType())
  //invariant(field == sizeof(TEMPLATE))
  //invariant(field == sizeof(ThisType))
  int field;

  invariant(ubound((ThisType *) buf) >= 10)
  int *buf;
};

int makeStruct()
{
  templateStruct<double> s;
  return s.SizeOfType();
}

template <typename TEMPLATE>
TEMPLATE* makeValue()
{
  assume_static(sizeof(TEMPLATE) > 0);
  return (TEMPLATE*)0;
}

int* makeInt()
{
  return makeValue<int>();
}
