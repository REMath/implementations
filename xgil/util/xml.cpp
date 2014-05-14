
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

#include "xml.h"
#include "primitive.h"

NAMESPACE_XGILL_BEGIN

void WriteXMLOpenTag(Buffer *buf, const char *tag)
{
  buf->Append("<", 1);
  buf->Append(tag, strlen(tag));
  buf->Append(">", 1);
}

void WriteXMLCloseTag(Buffer *buf, const char *tag)
{
  buf->Append("</", 2);
  buf->Append(tag, strlen(tag));
  buf->Append(">", 1);
}

void WriteXMLTagString(Buffer *buf, const char *tag, const char *value)
{
  WriteXMLOpenTag(buf, tag);

  // escape <, >, & characters.
  const char *pos = value;
  while (*pos) {
    switch (*pos) {
    case '<':
      buf->Append("&lt;", 4); break;
    case '>':
      buf->Append("&gt;", 4); break;
    case '&':
      buf->Append("&amp;", 5); break;
    case '\n':
      buf->Append("\\n", 2); break;
    default:
      buf->Append(pos, 1); break;
    }
    pos++;
  }

  WriteXMLCloseTag(buf, tag);
}

void WriteXMLTagInt(Buffer *buf, const char *tag, long value)
{
  mpz_t mpz;
  mpz_init_set_si(mpz, value);
  WriteXMLTagInt(buf, tag, mpz);
  mpz_clear(mpz);
}

void WriteXMLTagInt(Buffer *buf, const char *tag, const mpz_t value)
{
  WriteXMLOpenTag(buf, tag);
  IntToString(buf, value);

  // remove the trailing NULL added by IntToString.
  buf->pos--;

  WriteXMLCloseTag(buf, tag);
}

NAMESPACE_XGILL_END
