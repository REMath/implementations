
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

#include "primitive.h"
#include <errno.h>

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// String static
/////////////////////////////////////////////////////////////////////

HashCons<String> String::g_table;

int String::Compare(const String *s0, const String *s1)
{
  return strcmp(s0->m_value, s1->m_value);
}

String* String::Copy(const String *s)
{
  return new String(*s);
}

void String::Write(Buffer *buf, const String *s)
{
  WriteString(buf, (const uint8_t*) s->m_value,
              strlen(s->m_value) + 1);
}

String* String::Read(Buffer *buf)
{
  const uint8_t *str_base = NULL;
  size_t str_len = 0;

  if (!ReadString(buf, &str_base, &str_len))
    return NULL;

  if (str_len == 0 || str_base[str_len - 1] != '\0')
    return NULL;

  return Make((const char*) str_base);
}

void String::WriteWithTag(Buffer *buf, const String *s, tag_t tag)
{
  WriteOpenTag(buf, tag);
  Write(buf, s);
  WriteCloseTag(buf, tag);
}

String* String::ReadWithTag(Buffer *buf, tag_t tag)
{
  if (!ReadOpenTag(buf, tag))
    return NULL;

  String *s = Read(buf);
  if (s == NULL)
    return NULL;

  if (!ReadCloseTag(buf, tag))
    return NULL;

  return s;
}

void String::WriteCache(Buffer *buf, String *s)
{
  WriteOpenTag(buf, TAG_CacheString);
  uint32_t id = 0;
  if (buf->TestSeen((uint64_t)s, &id)) {
    WriteUInt32(buf, id);
  }
  else {
    Write(buf, s);
    WriteUInt32(buf, id);
  }
  WriteCloseTag(buf, TAG_CacheString);
}

String* String::ReadCache(Buffer *buf)
{
  uint32_t id = 0;
  String *s = NULL;

  Try(ReadOpenTag(buf, TAG_CacheString));
  if (ReadUInt32(buf, &id)) {
    uint64_t v = 0;
    Try(buf->TestSeenRev((uint32_t)id, &v));
    s = (String*) v;
  }
  else {
    Try(s = Read(buf));
    Try(ReadUInt32(buf, &id));
    Try(buf->AddSeenRev(id, (uint64_t) s));
  }
  Try(ReadCloseTag(buf, TAG_CacheString));
  return s;
}

/////////////////////////////////////////////////////////////////////
// String
/////////////////////////////////////////////////////////////////////

String::String(const char *value)
  : m_value(value)
{
  Assert(m_value);
  m_hash = HashBlock(0, (const uint8_t*) m_value, strlen(m_value));
}

void String::Print(OutStream &out) const
{
  out << "\"";
  PrintString(out, (const uint8_t*)m_value, strlen(m_value));
  out << "\"";
}

void String::Persist()
{
  char *new_value = new char[strlen(m_value) + 1];
  strcpy(new_value, m_value);
  m_value = new_value;
}

void String::UnPersist()
{
  delete[] m_value;
  m_value = NULL;
}

/////////////////////////////////////////////////////////////////////
// DataString static
////////////////////////////////////////////////////////////////////

HashCons<DataString> DataString::g_table;

int DataString::Compare(const DataString *s0, const DataString *s1)
{
  TryCompareValues(s0->m_value_length, s1->m_value_length);
  return memcmp(s0->m_value, s1->m_value, s0->m_value_length);
}

DataString* DataString::Copy(const DataString *s)
{
  return new DataString(*s);
}

void DataString::Write(Buffer *buf, const DataString *s)
{
  WriteString(buf, s->m_value, s->m_value_length);
}

DataString* DataString::Read(Buffer *buf)
{
  const uint8_t *str_base = NULL;
  size_t str_len = 0;

  if (!ReadString(buf, &str_base, &str_len))
    return NULL;

  return Make(str_base, str_len);
}

/////////////////////////////////////////////////////////////////////
// DataString
/////////////////////////////////////////////////////////////////////

DataString::DataString(const uint8_t *value, size_t value_length)
  : m_value(value), m_value_length(value_length)
{
  m_hash = HashBlock(0, m_value, m_value_length);
}

void DataString::Print(OutStream &out) const
{
  out << "D\"";
  PrintString(out, m_value, m_value_length);
  out << "\"";
}

void DataString::Persist()
{
  uint8_t *new_value = new uint8_t[m_value_length];
  memcpy(new_value, m_value, m_value_length);
  m_value = new_value;
}

void DataString::UnPersist()
{
  delete[] m_value;
  m_value = NULL;
}

/////////////////////////////////////////////////////////////////////
// Location static
/////////////////////////////////////////////////////////////////////

HashCons<Location> Location::g_table;

int Location::Compare(const Location *l0, const Location *l1)
{
  TryCompareObjects(l0->m_filename, l1->m_filename, String);
  TryCompareValues(l0->m_line, l1->m_line);
  return 0;
}

Location* Location::Copy(const Location *l)
{
  return new Location(*l);
}

void Location::Write(Buffer *buf, const Location *l)
{
  WriteOpenTag(buf, TAG_Location);
  String::WriteCache(buf, l->FileName());
  WriteUInt32(buf, l->Line());
  WriteCloseTag(buf, TAG_Location);
}

Location* Location::Read(Buffer *buf)
{
  String *filename = NULL;
  uint32_t line = 0;

  Try(ReadOpenTag(buf, TAG_Location));
  Try(filename = String::ReadCache(buf));
  Try(ReadUInt32(buf, &line));
  Try(ReadCloseTag(buf, TAG_Location));

  return Make(filename, line);
}

/////////////////////////////////////////////////////////////////////
// Location
/////////////////////////////////////////////////////////////////////

Location::Location(String *filename, uint32_t line)
  : m_filename(filename), m_line(line)
{
  m_hash = Hash32(m_filename->Hash(), m_line);
}

void Location::Print(OutStream &out) const
{
  out << "\"" << m_filename->Value() << ":" << (long)m_line << "\"";
}

void Location::MarkChildren() const
{
  m_filename->Mark();
}

NAMESPACE_XGILL_END
