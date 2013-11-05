
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

#include "config.h"
#include "hashtable.h"
#include <stdint.h>

NAMESPACE_XGILL_BEGIN

// functionality for monitoring analysis resource usage.

// soft memory limit for the process, in MB. when usage goes above this
// caches will be cleaned out to bring usage back below (hopefully).
extern ConfigOption memory_limit;

// print the virtual memory usage of this process.
void PrintVmUsage();

// virtual memory usage exceeds the soft memory limit.
bool IsHighVmUsage();

// virtual memory usage exceeds 2/3 of the soft memory limit.
bool IsModerateVmUsage();

NAMESPACE_XGILL_END
