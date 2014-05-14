// cyctimer.cc            see license.txt for copyright and terms of use
// code for cyctimer.h

#include "cyctimer.h"    // this module
#include "cycles.h"      // getCycles_ll
#include "nonport.h"     // getMilliseconds

#include <stdio.h>       // sprintf


CycleTimer::CycleTimer()
{
  // I make the cycle timer the inner of the two, since presumably
  // it's more precise, so shouldn't measure the time taken to issue
  // the getMilliseconds() call (which might involve a system call
  // on some systems)
  startMilliseconds = getMilliseconds();
  startCycles = getCycles_ll();
}


string CycleTimer::elapsed() const
{
  unsigned long long cycles = getCycles_ll() - startCycles;
  unsigned long ms = getMilliseconds() - startMilliseconds;

  // I print the cycles with an underscore separating the millions
  // from the rest because it's easier to read that way (and because
  // on a 1GHz machine, like mine, it's where the decimal point goes
  // when interpreting it as milliseconds)
  char buf[80];
  sprintf(buf, "%lu ms, %llu_%06llu cycles",
               ms, cycles/1000000, cycles%1000000);

  return string(buf);     // makes a copy
}


// --------------------- test code ----------------
#ifdef TEST_CYCTIMER

#include <unistd.h>    // sleep

int main()
{
  {
    CycleTimer timer;
    string s = timer.elapsed();
    printf("short time: %s\n", s.pcharc());
  }

  {
    CycleTimer timer;
    sleep(1);
    string s = timer.elapsed();
    printf("one second: %s\n", s.pcharc());
  }
  
  {
    CycleTimer timer;
    sleep(2);
    string s = timer.elapsed();
    printf("two seconds: %s\n", s.pcharc());
  }

  return 0;
}


#endif // TEST_CYCTIMER
