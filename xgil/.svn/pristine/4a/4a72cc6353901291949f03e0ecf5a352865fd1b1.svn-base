// serialno.cc
// code for serialno.h

#include "serialno.h"         // this module
#include "trace.h"            // tracingSys


// -------------------- serial numbers ON --------------------
#if USE_SERIAL_NUMBERS

SerialBase::SerialBase()
  : serialNumber(incSerialNumber())
{}


// I define this function so that even the copy ctor will get
// and use a unique serial number
SerialBase::SerialBase(SerialBase const &obj)
  : serialNumber(incSerialNumber())
{}


SerialBase& SerialBase::operator= (SerialBase const &)
{
  // do *not* copy the serial number
  return *this;
}


int globalSerialNumber = 0;


int incSerialNumber()
{
  // put the value into a local variable so that (at least when
  // optimization is turned off) there is an easy name to use
  // for conditional breakpoints
  int sn = globalSerialNumber++;

  // NOTE: put the breakpoint ABOVE the previous line, NOT HERE!
  return sn;
}


string printSerialNo(char const *pre, int num, char const *post)
{
  if (tracingSys("serialNumbers")) {
    return stringc << pre << num << post;
  }
  else {
    return "";
  }
}


#endif // USE_SERIAL_NUMBERS



// -------------------- serial numbers OFF --------------------
// nothing..


// EOF
