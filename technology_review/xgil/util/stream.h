
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

// replacements for the standard library ostream and istream interfaces.
// these classes are being replaced because, a) we don't otherwise have
// any dependencies on the standard library, and b) using them requires
// us to pull in pieces of the standard library we don't want, such as
// std::string (which doesn't play nice with a globally overloaded
// 'operator new', at least in GCC).

// except for the name of the class (OutStream vs. ostream),
// cout/cerr/etc. have the same name so code using these classes should
// look the same as that using the standard library streams.
// this is to make it easier to port code that is using the standard library.

#include "istream.h"
#include "ostream.h"
