
// Sixgill: Static assertion checker for C/C++ programs.
// Copyright (C) 2009-2010  Stanford University
// Author: Brian Hackett
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include "alloc.h"
#include "ostream.h"
#include <stdio.h>
#include <unistd.h>

// namespace definitions

#define NAMESPACE_XGILL_BEGIN  namespace Xgill {
#define NAMESPACE_XGILL_END    }
#define NAMESPACE_XGILL_USING  using namespace Xgill;

#define NAMESPACE_BEGIN(NAME)  namespace NAME {
#define NAMESPACE_END(NAME)    }

// assertion definitions

// flag indicating whether to pause instead of abort at a failed assertion.
// pausing will keep the process from terminating and allow a stack trace
// to be extracted via gdb. this is off by default, and should only be used
// in cases where an assertion failure is unrecoverable for the whole system.
extern bool g_pause_assertions;

__attribute__((noreturn))
inline void AssertFail(const char *file, int line, const char *func,
                       const char *msg)
{
  fprintf(logfile, "%s: %d: %s: Assertion '%s' failed.\n", file, line, func, msg);
  fflush(logfile);
  //if (g_pause_assertions)
  //  pause();
  abort();
}

#define Assert(cond)                                            \
  do {                                                          \
    if (!(cond)) {                                              \
      AssertFail(__FILE__, __LINE__, __FUNCTION__, #cond);      \
    }                                                           \
  } while (0)

#define AssertArray(t, len)                     \
  do {                                          \
    Assert(t);                                  \
    for (size_t ind = 0; ind < len; ind++) {    \
      Assert((t)[ind]);                         \
    }                                           \
  } while (0)

#define AssertOptionalArray(t, len)             \
  do {                                          \
    if (len > 0) {                              \
      Assert(t);                                \
      for (size_t ind = 0; ind < len; ind++) {  \
        Assert((t)[ind]);                       \
      }                                         \
    }                                           \
  } while (0)

// if action returns 0 then fail. the action must run regardless
// of whether Assert is enabled.
#define Try(action) do { if (!(action)) Assert(false); } while (0)

// allow disabling the breakpoint as the library defining Breakpoint
// might not be linked in.
#ifndef XGILL_NO_BREAKPOINT

// call a function to which gdb won't get confused when trying to set a
// breakpoint. this has to be extern to keep it from being inlined.
void Breakpoint(void *v = NULL);

#endif // XGILL_NO_BREAKPOINT
