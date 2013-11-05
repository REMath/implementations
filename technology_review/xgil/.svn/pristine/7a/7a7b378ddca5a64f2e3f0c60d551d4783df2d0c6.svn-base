
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

// emission of simple XML tags (plain tags, no attributes)

#include "buffer.h"

NAMESPACE_XGILL_BEGIN

void WriteXMLOpenTag(Buffer *buf, const char *tag);
void WriteXMLCloseTag(Buffer *buf, const char *tag);
void WriteXMLTagString(Buffer *buf, const char *tag, const char *value);
void WriteXMLTagInt(Buffer *buf, const char *tag, const mpz_t value);
void WriteXMLTagInt(Buffer *buf, const char *tag, long value);

NAMESPACE_XGILL_END
