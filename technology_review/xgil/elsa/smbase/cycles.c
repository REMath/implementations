// cycles.c            see license.txt for copyright and terms of use
// code for cycles.h

#include "cycles.h"      // this module

// -------------------- x86 -------------------------
#if defined(__i386__)
// use the 'rdtsc' (read time-stamp count) instruction
// NOTE: this entire file assumes we're compiling to a 32-bit machine
// (i.e. 'unsigned' is a 32-bit quantity)

// see also:
//   http://cedar.intel.com/software/idap/media/pdf/rdtscpm1.pdf
//   http://www.x86-64.org/lists/bugs/msg00621.html
//   http://www.dc.uba.ar/people/materias/oc2/LaboLinux/docs/intel/RDTSC.pdf


#ifdef RDTSC_SOURCE
// this function yields a 64-bit cycle count, writing into
// two variables passed by address
void getCycles(unsigned *lowp, unsigned *highp)
{
  unsigned int low, high;

  // this is gcc inline assembler syntax; it says that the
  // instruction writes to EAX ("=a") and EDX ("=d"), but that
  // I would like it to then copy those values into 'low' and
  // 'high', respectively
  asm volatile ("rdtsc" : "=a" (low), "=d" (high));

  // now copy into the variables passed by address
  *lowp = low;
  *highp = high;
}

#else // RDTSC_SOURCE

// this is the binary instructions that gcc-2.95.3 (optimization -O2)
// produces for the above code; it will work regardless of the current
// compiler's assembler syntax (even if the current compiler doesn't
// have *any* inline assembler)
static char const rdtsc_instructions[] = {
  0x55,                                 // push   %ebp
  0x89, 0xe5,                           // mov    %esp,%ebp
  0x53,                                 // push   %ebx
  0x8b, 0x4d, 0x08,                     // mov    0x8(%ebp),%ecx
  0x8b, 0x5d, 0x0c,                     // mov    0xc(%ebp),%ebx
  0x0f, 0x31,                           // rdtsc
  0x89, 0x01,                           // mov    %eax,(%ecx)
  0x89, 0x13,                           // mov    %edx,(%ebx)
  0x5b,                                 // pop    %ebx
  0xc9,                                 // leave
  0xc3,                                 // ret
  0x90,                                 // nop
};

// external entry point
void getCycles(unsigned *lowp, unsigned *highp)
{
  return ((void (*)(unsigned*, unsigned*))rdtsc_instructions)(lowp, highp);
}

#endif // RDTSC_SOURCE


// ------------------ unknown architecture -----------------
#else

// some preprocessors choke on this..
//#warn unknown architecture in cycles.c

void getCycles(unsigned *lowp, unsigned *highp)
{
  *lowp = 0;
  *highp = 0;
}

#endif // architecture


// ------------------- getCycles_ll ----------------------
#ifdef __GNUC__
// this uses gcc's "long long" to represent the 64-bit
// quantity a little more easily
unsigned long long getCycles_ll()
{
  unsigned int low, high;
  unsigned long long ret;

  getCycles(&low, &high);

  ret = high;
  ret <<= 32;
  ret += low;

  return ret;
}
#endif // __GNUC__


// ----------------------- test code ---------------------
#ifdef TEST_CYCLES

#include <stdio.h>    // printf

int main()
{
  #ifdef __GNUC__
    unsigned long long v = getCycles_ll();
    printf("getCycles: %llu\n", v);
  #endif // __GNUC__

  // this segment should work on any compiler, by virtue
  // of only using 32-bit quantities
  {
    unsigned low, high;
    getCycles(&low, &high);
    printf("getCycles high=%u, low=%u\n", high, low);
  }

  // test whether the instruction causes a privileged instruction
  // fault; on my machine I get 33 cycles per call, which clearly
  // is too few for it to be trapping on each one
  {
    unsigned low1, low2, low3, high;
    getCycles(&low1, &high);
    getCycles(&low2, &high);
    getCycles(&low3, &high);
    printf("three lows in a row: %u, %u, %u\n", low1, low2, low3);
  }

  return 0;
}
#endif // TEST_CYCLES
