
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

#include "monitor.h"

#include <unistd.h>

NAMESPACE_XGILL_BEGIN

ConfigOption memory_limit(CK_UInt, "memory-limit", "0",
                          "Soft process memory limit, in MB (0 == no limit)");

// get the amount of virtual memory this process is using, in megabytes.
// returns 0 if the amount could not be determined. only includes memory
// that has been heap-allocated but not yet freed, i.e. omits memory
// allocated for this process but either:
// - not in use
// - used for the stack
// - used for heap allocator control structures
// the number reported is smaller than but usually close to the complete
// usage reported by, e.g. 'ps aux'
uint32_t GetVmUsage()
{
  return g_alloc_total >> 20;
}

void PrintVmUsage()
{
  logout << "VM Usage: " << GetVmUsage() << " mB" << endl;
}

bool IsHighVmUsage()
{
  uint32_t limit = memory_limit.UIntValue();
  if (limit == 0)
    return false;

  uint32_t mb_usage = GetVmUsage();
  return mb_usage > limit;
}

bool IsModerateVmUsage()
{
  uint32_t limit = memory_limit.UIntValue();
  if (limit == 0)
    return false;

  uint32_t mb_usage = GetVmUsage();
  return mb_usage > limit * 2 / 3;
}

NAMESPACE_XGILL_END
