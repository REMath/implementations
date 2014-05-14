
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

// layout of XDb files

#include <util/buffer.h>

NAMESPACE_XGILL_BEGIN

extern TrackAlloc g_alloc_XdbStreamInfo;
extern TrackAlloc g_alloc_XdbStreamInfoKey;

namespace XdbFile {

  // stream description layout

  // a stream is a contiguous range of bytes in the underlying file,
  // with a prefix that is actually in use and a remainder that is
  // available but unused. except for the header at the beginning of
  // the file (see below), the file is a contiguous series of streams
  // where one stream begins immediately after the previous stream ends.

  // streams are described by a 28 byte structure with the following layout:

  // 0..3    1-indexed stream identifier (0 is null stream)
  // 4..11   absolute offset into file of stream base
  // 12..15  allocated size of stream
  // 16..19  length of in-use portion of stream
  // 20..23  identifier of previous stream in file
  // 24..27  identifier of next stream in file

  #define XDB_STREAM_LAYOUT_SIZE 28

  struct StreamLayout
  {
    uint32_t id;
    uint64_t offset;
    uint32_t size;
    uint32_t length;
    uint32_t prev_id;
    uint32_t next_id;

    StreamLayout();
    void Read(Buffer *buf);
    void Write(Buffer *buf) const;
  };

  // header layout

  // ASCII for XDB\0
  #define XDB_MAGIC  0x58444200

  // version number
  #define XDB_VERSION  1

  // numbering of special streams and data streams
  #define XDB_HASH_STREAM        1
  #define XDB_KEY_STREAM         2
  #define XDB_DATA_STREAM_BEGIN  3

  // the file header at the beginning of the file describes the
  // form of the consists of
  // the following structures:

  // 0..3    XDB magic number
  // 4..7    XDB version number
  // 8..11   header size
  // 12..19  file size
  // 20..23  number of data streams
  // 24..27  hash method code for values in hash stream
  // 28..55  layout of hash stream
  // 56..83  layout of key stream
  // 84..87  identifier of first stream in file
  // 88..91  identifier of last stream in file

  // ASCII for ELF\0
  #define XDB_HASH_ELF  0x454c4600

  #define XDB_HEADER_MIN_SIZE 92

  struct FileHeader
  {
    uint32_t magic;
    uint32_t version;
    uint32_t header_size;
    uint64_t file_size;
    uint32_t data_stream_count;
    uint32_t hash_method;
    StreamLayout hash_stream;
    StreamLayout key_stream;
    uint32_t first_id;
    uint32_t last_id;

    FileHeader();
    void Read(Buffer *buf);
    void Write(Buffer *buf) const;
  };

  // hash stream

  // the hash stream contains 8 bytes for each data stream, in the order
  // in which the streams are numbered (the first entry in the hash
  // stream is for stream XDB_DATA_STREAM_BEGIN). the length of the
  // hash stream is 8 * the number of data streams.

  // 0..3  32-bit hash value of key for this stream
  // 4..7  offset into key stream of data for this stream

  #define XDB_HASH_STREAM_ENTRY_SIZE  8

  struct HashStreamEntry
  {
    uint32_t hash_value;
    uint32_t key_offset;

    HashStreamEntry();
    void Read(Buffer *buf);
    void Write(Buffer *buf) const;
  };

  // key stream

  // the key stream contains a variable number of bytes for each
  // data stream, in an arbitrary order (though typically the order
  // in which the streams are numbered).

  // 0..27   layout of the data stream for this key
  // 28..31  32-bit length of the key
  // 32..?   contents of the key (number of bytes equal to length)

  // offset into the key stream entry of the data stream layout,
  // for when we don't care about the key string itself.
  #define XDB_KEY_STREAM_LAYOUT_OFFSET  0

  // default size of buffer to read key data from.
  // in most cases this is sufficient to get the entire key;
  // if not, the key field of the entry will be NULL after reading.
  #define XDB_KEY_STREAM_TRY_SIZE  1024

  // length of key stream entry when the key has the specified length.
  #define XDB_KEY_STREAM_ENTRY_SIZE(LEN)  (32 + LEN)

  // minimum size of an entry that is reallocated at least once.
  #define REALLOCATE_MIN_SIZE  512

  struct KeyStreamEntry
  {
    StreamLayout data_stream;

    // allocated with new[] by Read()
    uint8_t *key;
    uint32_t key_length;

    KeyStreamEntry();
    void Read(Buffer *buf);
    void Write(Buffer *buf) const;
  };

  // data streams (identifier 3+)

  // the data streams are exactly those strings which are associated
  // with the key, with no metadata.

  // validity

  bool IsValidFileHeader(const FileHeader &head);
  bool IsValidStreamLayout(const FileHeader &head, const StreamLayout &str);

} // end namespace XdbFile

NAMESPACE_XGILL_END
