// serialno.h
// object serial number

// The idea here is that it's sometimes difficult during debugging to
// keep track of the various objects (e.g. Types) floating around, and
// virtual addresses are not so stable.  So, by turning on
// USE_SERIAL_NUMBERS, every object will get a unique serial number,
// and (some of) the print routines will print the number.  Normally
// this should be off since it uses memory and makes the printouts
// ugly.

#ifndef SERIALNO_H
#define SERIALNO_H

#include "str.h"        // string

// default to off; can turn on via "./configure -useSerialNumbers"
#ifndef USE_SERIAL_NUMBERS
  #define USE_SERIAL_NUMBERS 0
#endif

#ifdef USE_SERIAL_NUMBERS
  #if USE_SERIAL_NUMBERS!=0 && USE_SERIAL_NUMBERS!=1
    #error USE_SERIAL_NUMBERS defined but not 0 or 1
  #endif
#endif


#if USE_SERIAL_NUMBERS

  // base class for classes that want serial numbers to inherit
  class SerialBase {
  public:      // data
    // unique across all objects
    int serialNumber;

  public:      // funcs
    SerialBase();
    SerialBase(SerialBase const &obj);
    SerialBase& operator= (SerialBase const &obj);
  };

  #define INHERIT_SERIAL_BASE     : public SerialBase
  #define INHERIT_SERIAL_BASE_AND : public SerialBase ,

  // global counter, starts at 0
  extern int globalSerialNumber;

  // get the next serial number
  int incSerialNumber();

  // return a string with 'pre', then the number, then 'post'
  //
  // NOTE: Currently, the tracing flag "serialNumbers" must be set
  // for the printouts to include the serial numbers.  (When it is
  // not set, this function just returns "".)
  string printSerialNo(char const *pre, int num, char const *post);

#else // !USE_SERIAL_NUMBERS

  // variations of above for use when serial numbers are disabled

  #define INHERIT_SERIAL_BASE
  #define INHERIT_SERIAL_BASE_AND :

#endif // !USE_SERIAL_NUMBERS


#endif // SERIALNO_H
