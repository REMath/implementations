
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

// primitive front-end types

#include <util/hashcons.h>
#include <util/buffer.h>

NAMESPACE_XGILL_BEGIN

// base string/int/float constant primitives

// string that is NULL-terminated
class String : public HashObject
{
 public:
  static int Compare(const String *s0, const String *s1);
  static String* Copy(const String *s);
  static void Write(Buffer *buf, const String *s);
  static String* Read(Buffer *buf);

  // write/read a String surrounded by an outer tag
  static void WriteWithTag(Buffer *buf, const String *s, tag_t tag);
  static String* ReadWithTag(Buffer *buf, tag_t tag);

  // write/read a String cached with the Buffer TestSeen mechanism
  static void WriteCache(Buffer *buf, String *s);
  static String* ReadCache(Buffer *buf);

  static String* Make(const char *value) {
    String xs(value);
    return g_table.Lookup(xs);
  }

 public:
  // get the value of this string
  const char* Value() const { return m_value; }

  // inherited methods
  void Print(OutStream &out) const;
  void Persist();
  void UnPersist();

 private:
  const char *m_value;

  String(const char *value);
  static HashCons<String> g_table;
};

// string data that is *NOT* necessarily NULL-terminated
class DataString : public HashObject
{
 public:
  static int Compare(const DataString *s0, const DataString *s1);
  static DataString* Copy(const DataString *s);
  static void Write(Buffer *buf, const DataString *s);
  static DataString* Read(Buffer *buf);

  static DataString* Make(const uint8_t *value, size_t value_length) {
    DataString xs(value, value_length);
    return g_table.Lookup(xs);
  }

 public:
  // get the value/length of this string
  size_t ValueLength() const { return m_value_length; }
  const uint8_t* Value() const { return m_value; }

  // inherited methods
  void Print(OutStream &out) const;
  void Persist();
  void UnPersist();

 private:
  const uint8_t *m_value;
  size_t m_value_length;

  DataString(const uint8_t *value, size_t value_length);
  static HashCons<DataString> g_table;
};

// source program filename/line#
class Location : public HashObject
{
 public:
  static int Compare(const Location *l0, const Location *l1);
  static Location* Copy(const Location *l);
  static void Write(Buffer *buf, const Location *l);
  static Location* Read(Buffer *buf);

  static Location* Make(String *filename, uint32_t line) {
    Location xl(filename, line);
    return g_table.Lookup(xl);
  }

 public:
  // get the filename/line of this location
  String* FileName() const { return m_filename; }
  uint32_t Line() const { return m_line; }

  // get the filename of this location, stripping off any directory.
  const char* ShortFileName() {
    const char *pos = m_filename->Value();
    while (const char *npos = strchr(pos, '/'))
      pos = npos + 1;
    return pos;
  }

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;

 private:
  String *m_filename;
  uint32_t m_line;

  Location(String *filename, uint32_t line);
  static HashCons<Location> g_table;
};

// serialization tags

// generic tags usable by multiple intermediate nodes.
// each contains a single TAG_UInt32
#define TAG_Kind    100
#define TAG_OpCode  102
#define TAG_Width   104
#define TAG_Offset  106
#define TAG_Count   108
#define TAG_Index   110

// generic sign tag. empty, only specified if something is signed.
#define TAG_Sign    112

// generic name tag, contains a TAG_String.
#define TAG_Name    114

// generic true/false tag, empty contents.
#define TAG_True    116
#define TAG_False   118

// debugging tag containing a TAG_UInt32 hash code.
#define TAG_Hash    120

// cached string tag. contains either a TAG_String followed by a TAG_UInt32,
// in which case the int gives an ID for the string, or a TAG_UInt32,
// indicating the ID for a string generated previously in the stream.
#define TAG_CacheString  130

// children: TAG_CacheString, TAG_UInt32
#define TAG_Location  140

NAMESPACE_XGILL_END
