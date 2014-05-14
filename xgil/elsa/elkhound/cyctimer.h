// cyctimer.h            see license.txt for copyright and terms of use
// simple cycles/milliseconds timer

#ifndef CYCTIMER_H
#define CYCTIMER_H

#include "str.h"           // string

class CycleTimer {
public:
  unsigned long long startCycles;
  unsigned long startMilliseconds;
  
public:
  CycleTimer();            // starts timer
  string elapsed() const;  // formats elapsed time as "NN ms, NN_NNNNNN cycles"
};

#endif // CYCTIMER_H
