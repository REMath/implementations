
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

#include "layout.h"
#include <unistd.h>

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// StreamLayout
/////////////////////////////////////////////////////////////////////

XdbFile::StreamLayout::StreamLayout()
{
  memset(this, 0, sizeof(*this));
}

void XdbFile::StreamLayout::Read(Buffer *buf)
{
  if (!buf->HasRemaining(XDB_STREAM_LAYOUT_SIZE))
    return;

  Read32(buf, &id);
  Read64(buf, &offset);
  Read32(buf, &size);
  Read32(buf, &length);
  Read32(buf, &prev_id);
  Read32(buf, &next_id);
}

void XdbFile::StreamLayout::Write(Buffer *buf) const
{
  buf->Ensure(XDB_STREAM_LAYOUT_SIZE);

  Write32(buf, id);
  Write64(buf, offset);
  Write32(buf, size);
  Write32(buf, length);
  Write32(buf, prev_id);
  Write32(buf, next_id);
}

/////////////////////////////////////////////////////////////////////
// FileHeader
/////////////////////////////////////////////////////////////////////

XdbFile::FileHeader::FileHeader()
{
  memset(this, 0, sizeof(*this));
}

void XdbFile::FileHeader::Read(Buffer *buf)
{
  if (!buf->HasRemaining(XDB_HEADER_MIN_SIZE))
    return;

  Read32(buf, &magic);
  Read32(buf, &version);
  Read32(buf, &header_size);
  Read64(buf, &file_size);
  Read32(buf, &data_stream_count);
  Read32(buf, &hash_method);
  hash_stream.Read(buf);
  key_stream.Read(buf);
  Read32(buf, &first_id);
  Read32(buf, &last_id);
}

void XdbFile::FileHeader::Write(Buffer *buf) const
{
  Write32(buf, magic);
  Write32(buf, version);
  Write32(buf, header_size);
  Write64(buf, file_size);
  Write32(buf, data_stream_count);
  Write32(buf, hash_method);
  hash_stream.Write(buf);
  key_stream.Write(buf);
  Write32(buf, first_id);
  Write32(buf, last_id);
}

/////////////////////////////////////////////////////////////////////
// HashStreamEntry
/////////////////////////////////////////////////////////////////////

XdbFile::HashStreamEntry::HashStreamEntry()
{
  memset(this, 0, sizeof(*this));
}

void XdbFile::HashStreamEntry::Read(Buffer *buf)
{
  if (!buf->HasRemaining(8))
    return;

  Read32(buf, &hash_value);
  Read32(buf, &key_offset);
}

void XdbFile::HashStreamEntry::Write(Buffer *buf) const
{
  Write32(buf, hash_value);
  Write32(buf, key_offset);
}

/////////////////////////////////////////////////////////////////////
// KeyStreamEntry
/////////////////////////////////////////////////////////////////////

XdbFile::KeyStreamEntry::KeyStreamEntry()
{
  memset(this, 0, sizeof(*this));
}

void XdbFile::KeyStreamEntry::Read(Buffer *buf)
{
  if (!buf->HasRemaining(XDB_STREAM_LAYOUT_SIZE + 4))
    return;

  data_stream.Read(buf);

  Read32(buf, &key_length);
  if (!buf->HasRemaining(key_length)) {
    // leave the key_length intact so the caller knows how
    // much space to read when retrying
    return;
  }

  key = track_new<uint8_t>(g_alloc_XdbStreamInfoKey, key_length);
  memcpy(key, buf->pos, key_length);
  buf->pos += key_length;
}

void XdbFile::KeyStreamEntry::Write(Buffer *buf) const
{
  Assert(key);

  data_stream.Write(buf);
  Write32(buf, key_length);
  buf->Append(key, key_length);
}

/////////////////////////////////////////////////////////////////////
// Validity functions
/////////////////////////////////////////////////////////////////////

#define Test(cond)  do { if (!(cond)) return false; } while (0)

bool XdbFile::IsValidFileHeader(const FileHeader &head)
{
  Test(head.magic == XDB_MAGIC);
  Test(head.version == XDB_VERSION);
  Test(head.header_size >= XDB_HEADER_MIN_SIZE);
  Test(head.file_size >= head.header_size);

  Test(head.hash_method == XDB_HASH_ELF);

  Test(IsValidStreamLayout(head, head.hash_stream));
  Test(IsValidStreamLayout(head, head.key_stream));

  Test(head.hash_stream.length ==
      head.data_stream_count * XDB_HASH_STREAM_ENTRY_SIZE);

  Test(head.first_id != 0);
  Test(head.last_id != 0);

  Test(head.first_id < head.data_stream_count + XDB_DATA_STREAM_BEGIN);
  Test(head.last_id < head.data_stream_count + XDB_DATA_STREAM_BEGIN);

  return true;
}

bool XdbFile::IsValidStreamLayout(const FileHeader &head,
                                  const StreamLayout &str)
{
  Test(str.id != 0);
  Test(str.id < head.data_stream_count + XDB_DATA_STREAM_BEGIN);

  Test(str.offset >= head.header_size);
  Test(str.offset + (uint64_t) str.size <= head.file_size);
  Test(str.length <= str.size);

  Test(str.prev_id < head.data_stream_count + XDB_DATA_STREAM_BEGIN);
  Test(str.next_id < head.data_stream_count + XDB_DATA_STREAM_BEGIN);

  Test(str.prev_id != 0 || str.id == head.first_id);
  Test(str.next_id != 0 || str.id == head.last_id);

  return true;
}

NAMESPACE_XGILL_END
