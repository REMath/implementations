// growbuf.cc            see license.txt for copyright and terms of use
// code for growbuf.h

#include "growbuf.h"      // this module

#include <string.h>       // memcpy

void GrowBuffer::append(byte const *str, int len)
{
  // test length
  int newLen = getDataLen() + len;
  if (newLen > getAllocated()) {
    // must grow
    int newAlloc = max(getAllocated(), 16);
    while (newLen > newAlloc) {
      newAlloc *= 2;      // would like an overflow test here..
    }

    setAllocated(newAlloc);
  }

  // do copy
  memcpy(getData()+getDataLen(), str, len);
  setDataLen(newLen);
}


// ----------------- test code ----------------
#ifdef TEST_GROWBUF
#include "test.h"

void entry()
{
  byte const str[] = "crazy like a mad cow!";
  int len = sizeof(str);

  GrowBuffer buf;
  loopi(10) {
    buf.append(str, len);
  }
  loopi(10) {
    if (0!=memcmp(str, buf.getData()+len*i, len)) {
      xfailure("buffer contents are wrong");
    }
  }
  cout << "growbuf ok\n";
}

USUAL_MAIN

#endif // TEST_GROWBUF
