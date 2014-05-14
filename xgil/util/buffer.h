
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

// Buffer class for extensible byte arrays. also includes functions
// for writing and reading binary XML into a buffer, and various other
// utility functions on strings and buffers.

#include "hashtable.h"
#include <stdint.h>

#include <gmp.h>

//#define TRACK_BUFFER_MEMORY

NAMESPACE_XGILL_BEGIN

#ifdef TRACK_BUFFER_MEMORY
extern TrackAlloc g_alloc_Buffer;
#endif

// format for binary XML-style tags.

// tags are 16-bit quantities in the binary stream.
// all tags are either primitive or complex.

// primitive tags are String, Int32, UInt32, WCache, and RCache.
// - String is followed by an unsigned 32-bit length,
//   then a number of bytes indicates by that length.
// - Int32 is followed by a signed 32-bit quantity.
// - UInt32 is followed by an unsigned 32-bit quantity.
// - WCache is followed by an unsigned 32-bit quantity.
//   this indicates a position in an object cache the parent
//   object should be written to.
// - RCache is followed by an unsigned 32-bit quantity.
//   this indicates a position in the object cache referred
//   to by a previous WCache in the stream.

// complex tags start at TAG_ComplexStart.
// all complex open tags do not have their low bit set (they are
// even numbers); their corresponding close tag is that open tag
// with its low bit set (the open tag + 1).
// the format is:
// OPEN-TAG (primitive-tag | complex-tag)* CLOSE-TAG

// for all 16-bit tags and 32-bit quantities,
// the byte order is little-endian.

#define TAG_String  2
#define TAG_Int32   4
#define TAG_UInt32  6
#define TAG_UInt64  8

#define TAG_ComplexStart 100

#define BadTag(tag)                                     \
  do {                                                  \
    logout << "ERROR: Unexpected tag: " << tag << endl; \
    Assert(false);                                      \
  } while (0)

// values of type tag_t MUST have their low bit clear.
typedef uint16_t tag_t;

struct Buffer
{
  // base pointer of the buffer.
  uint8_t *base;

  // current position into the buffer.
  uint8_t *pos;

  // overall size of buf_base.
  size_t size;

  // whether this is a resizable buffer which owns its data.
  bool ownsBuffer;

#ifdef TRACK_BUFFER_MEMORY
  // allocator used to manage the buffer contents. this is non-NULL iff
  // the buffer is resizable, and if base was allocated for this buffer.
  TrackAlloc *alloc;
#endif

  // make a non-resizable buffer for the specified data.
  Buffer(const void *data, size_t data_length)
    : base((uint8_t*) data), pos(base), size(data_length), ownsBuffer(false),
#ifdef TRACK_BUFFER_MEMORY
      alloc(NULL),
#endif
      seen(NULL), seen_next(0), seen_rev(NULL)
  {}

  // make and allocate data for a resizable buffer that is initially empty.
  Buffer(size_t initial_size = 4096)
    : base(NULL), pos(NULL), size(0), ownsBuffer(true),
#ifdef TRACK_BUFFER_MEMORY
      alloc(&g_alloc_Buffer),
#endif
      seen(NULL), seen_next(0), seen_rev(NULL)
  {
    if (initial_size)
      Reset(initial_size);
  }

  // make and allocate data for a resizable buffer that is initially empty
  // and uses the specified allocator.
  Buffer(const char *alloc_name)
    : base(NULL), pos(NULL), size(0), ownsBuffer(true),
#ifdef TRACK_BUFFER_MEMORY
      alloc(&LookupAlloc(alloc_name)),
#endif
      seen(NULL), seen_next(0), seen_rev(NULL)
  {
    Reset(4096);
  }

  // buffer copying not allowed.
  Buffer(const Buffer &) { Assert(false); }
  Buffer& operator = (const Buffer&) { Assert(false); return *this; }

  // deallocate the buffer's data if it is resizable.
  ~Buffer() { Reset(0); }

  // resets the buffer state.
  // if the buffer is not resizable the initial state will be restored.
  // if the buffer is resizable the buffer's size will be set to
  // a new size (setting initial_size == 0 will delete all allocated data).
  void Reset(size_t initial_size);

  // resets the buffer state, but does not change the allocated size
  // of a resizable buffer.
  void Reset();

  // expand the buffer to a new capacity. the buffer must be resizable.
  void Expand(size_t new_size);

  // return whether there is enough room in this buffer for 'needed' bytes.
  bool HasRemaining(size_t needed)
  {
    return (pos - base + needed <= size);
  }

  // ensure there is enough room in this buffer for 'needed' bytes.
  // if there is not enough room the buffer must be resizable.
  void Ensure(size_t needed)
  {
    if (!HasRemaining(needed))
      Expand(size * 2 + needed);
  }

  // append the specified data onto the end of this buffer. ensures there
  // is enough room for the data.
  void Append(const void *data, size_t data_length)
  {
    Ensure(data_length);
    memcpy(pos, data, data_length);
    pos += data_length;
  }

  // persistent state within a buffer. the seen/seen_rev table can be used to
  // remember data that previously appeared in the buffer, and instead
  // of writing or reading it again just write/read an integer identifier.
  // these tables will be NULL until they are actually used
  // (in most cases they won't be used at all).

  typedef uint64_t SeenKey;

  typedef HashTable< SeenKey, uint32_t, DataHash<SeenKey> > SeenTable;

  // table for use in writing. seen maps previously written pointers to
  // the identifiers associated with them. seen_next is the next unused
  // identifier.
  SeenTable *seen;
  uint32_t seen_next;

  // return whether v is already in the seen table. if so, returns v's
  // identifier through pid. if not, associates v with a new identifier and
  // returns that identifier through pid.
  bool TestSeen(SeenKey v, uint32_t *pid);

  typedef HashTable< uint32_t, SeenKey, DataHash<uint32_t> > SeenRevTable;

  // table for use in reading. seen_rev maps identifiers back to the
  // pointers associated with that identifier. normally seen_rev maps
  // a contiguous range of identifiers.
  SeenRevTable *seen_rev;

  // return whether id has already been associated with a value. if so,
  // returns the value associated with id. if not, associates id with v.
  bool AddSeenRev(uint32_t id, SeenKey v);

  // get the v with which id was associated, return false if none.
  bool TestSeenRev(uint32_t id, SeenKey *pv);

  ALLOC_OVERRIDE(g_alloc_Buffer);
};

// buffer streams

// output stream for appending data to a buffer. if you use this to generate
// NULL-terminated strings at buf->base, make sure to write a NULL terminator
// at the end as the output stream methods do not automatically do this.
class BufferOutStream : public OutStream {
 public:
  Buffer *m_buf;

  // make an output stream for the specified FILE.
  BufferOutStream(Buffer *buf) : m_buf(buf) {}

  void Put(const void *buf, size_t len) {
    m_buf->Append(buf, len);
  }

  // get the base pointer of this buffer. adds a NULL terminator if necessary.
  const char* Base() {
    m_buf->Ensure(1);

    // don't advance the buffer position.
    *(m_buf->pos) = 0;
    return (const char*) m_buf->base;
  }
};

// read the entire contents of the specified stream and append them to buf.
// adds a NULL terminator at the end of the stream if one is not present.
void ReadInStream(InStream &in, Buffer *buf);

// Utility methods. return value indicates an error occurred.

// useful helper for ReadInStream. tokenizes the in-use portion of buffer by
// splitting into strings separated by each occurrence of tok ('\n', say).
// destructively updates the buffer contents to insert NULL terminators;
// the strings added will be internal pointers to data in buf.
void SplitBufferStrings(Buffer *buf, char tok, Vector<char*> *strings);

// for these the buffer's base and pos values must be the same.
// for input buffers the range of data to uncompress/compress is
// [input->base, input->base + input->size>. for output buffers the pos
// will be advanced to the end of the uncompressed/compressed data.
void UncompressBuffer(Buffer *input, Buffer *output);
void CompressBuffer(Buffer *input, Buffer *output);

// as UncompressBuffer/CompressBuffer, except the input buffer range
// used is [input->base, input->pos>.
void UncompressBufferInUse(Buffer *input, Buffer *output);
void CompressBufferInUse(Buffer *input, Buffer *output);

// data is a NULL-terminated string with no intervening NULLs
// before data_length
bool ValidString(const uint8_t *data, size_t data_length);

// convert a string representing an integer using the various C/C++
// constant representations (base 10, hex, octal, char constants, etc.)
// to that underlying constant. return value is whether the translation
// succeeded. result is optional.
bool StringToInt(const char *str, mpz_t result);
bool StringToInt(const char *str, long *result);

// print an integer in base 10 to the specified buffer. NULL terminates buf.
void IntToString(Buffer *buf, const mpz_t value);

// print an integer in base 10 to the specified stream.
void PrintInt(OutStream &out, const mpz_t value);

// print mpz_t values directly to a stream.
inline OutStream& operator << (OutStream &out, const mpz_t value) {
  PrintInt(out, value);
  return out;
}

// get a string representation of the minimum and maximum values that
// can be represented in the given bits/sign.
const char* GetMinimumInteger(size_t bits, bool sign);
const char* GetMaximumInteger(size_t bits, bool sign);

// unescape a single quoted character literal or double quoted string literal.
// return value is whether the translation succeeded.
bool UnescapeCharLiteral(const char *str, char *result);
bool UnescapeStringLiteral(const char *str, Buffer *result);

// unescape HTML sequences in val: &amp; &lt; &gt;. the result is allocated
// using new[].
char* HtmlUnescape(const char *val);

// print a string to the specified stream, escaping non-printable characters.
void PrintString(OutStream &out, const uint8_t *str, size_t len);

// print the specified number of blank spaces.
void PrintPadding(OutStream &out, size_t pad_spaces);

// print the data in buf, ending at the first closing tag after the
// buffer's current position. returns the number of characters read from
// the buffer.
size_t PrintPartialBuffer(OutStream &out, Buffer *buf);

// print the data in buf as a JSON string.
void PrintJSONBuffer(OutStream &out, Buffer *buf);

// Primitive write/read methods. byte order of data is least-significant
// byte first. the buffer must have at least the specified number of bytes
// remaining.

inline void Write8(Buffer *buf, uint8_t val)
{
  buf->pos[0] = val;
  buf->pos += 1;
}

inline void Write16(Buffer *buf, uint16_t val)
{
  buf->pos[0] = (uint8_t) val;
  buf->pos[1] = (uint8_t) (val >> 8);
  buf->pos += 2;
}

inline void Write32(Buffer *buf, uint32_t val)
{
  buf->pos[0] = (uint8_t) val;
  buf->pos[1] = (uint8_t) (val >> 8);
  buf->pos[2] = (uint8_t) (val >> 16);
  buf->pos[3] = (uint8_t) (val >> 24);
  buf->pos += 4;
}

inline void Write64(Buffer *buf, uint64_t val)
{
  buf->pos[0] = (uint8_t) val;
  buf->pos[1] = (uint8_t) (val >> 8);
  buf->pos[2] = (uint8_t) (val >> 16);
  buf->pos[3] = (uint8_t) (val >> 24);
  buf->pos[4] = (uint8_t) (val >> 32);
  buf->pos[5] = (uint8_t) (val >> 40);
  buf->pos[6] = (uint8_t) (val >> 48);
  buf->pos[7] = (uint8_t) (val >> 56);
  buf->pos += 8;
}

inline void Read8(Buffer *buf, uint8_t *pval)
{
  *pval = buf->pos[0];
  buf->pos += 1;
}

inline void Read16(Buffer *buf, uint16_t *pval)
{
  uint16_t val = 0;
  val |= buf->pos[0];
  val |= buf->pos[1] << 8;
  *pval = val;

  buf->pos += 2;
}

inline void Read32(Buffer *buf, uint32_t *pval)
{
  uint32_t val = 0;
  val |= buf->pos[0];
  val |= buf->pos[1] << 8;
  val |= buf->pos[2] << 16;
  val |= buf->pos[3] << 24;
  *pval = val;

  buf->pos += 4;
}

inline void Read64(Buffer *buf, u_int64_t *pval)
{
  u_int64_t val = 0;
  val |= ((uint64_t)buf->pos[0]);
  val |= ((uint64_t)buf->pos[1]) << 8;
  val |= ((uint64_t)buf->pos[2]) << 16;
  val |= ((uint64_t)buf->pos[3]) << 24;
  val |= ((uint64_t)buf->pos[4]) << 32;
  val |= ((uint64_t)buf->pos[5]) << 40;
  val |= ((uint64_t)buf->pos[6]) << 48;
  val |= ((uint64_t)buf->pos[7]) << 56;
  *pval = val;

  buf->pos += 8;
}

// rewind a buffer by the specified number of bytes
inline void Rewind(Buffer *buf, size_t count)
{
  buf->pos -= count;
}

// Write methods. these always succeed

void WriteString(Buffer *buf, const uint8_t *str, size_t str_length);
void WriteInt32(Buffer *buf, int32_t val);
void WriteUInt32(Buffer *buf, uint32_t val);
void WriteUInt64(Buffer *buf, uint64_t val);
void WriteOpenTag(Buffer *buf, tag_t tag);
void WriteCloseTag(Buffer *buf, tag_t tag);

// write primitive values with open/close tag wrappers
void WriteTagString(Buffer *buf, tag_t tag,
                    const uint8_t *str, size_t str_length);
void WriteTagInt32(Buffer *buf, tag_t tag, int32_t val);
void WriteTagUInt32(Buffer *buf, tag_t tag, uint32_t val);
void WriteTagUInt64(Buffer *buf, tag_t tag, uint64_t val);
void WriteTagEmpty(Buffer *buf, tag_t tag);

// number of bytes used by WriteUInt32
#define UINT32_LENGTH 6

// Read methods. return value is true on success, false on failure.
// if false then the buffer state is rolled back to before the call

// stores the string base and length at pstr/psize.
// these will point into the buffer's contents.
bool ReadString(Buffer *buf, const uint8_t **pstr, size_t *psize);

bool ReadInt32(Buffer *buf, int32_t *pval);
bool ReadUInt32(Buffer *buf, uint32_t *pval);
bool ReadUInt64(Buffer *buf, uint64_t *pval);
bool ReadOpenTag(Buffer *buf, tag_t tag);
bool ReadCloseTag(Buffer *buf, tag_t tag);

// read primitive values with open/close tag wrappers
bool ReadTagString(Buffer *buf, tag_t tag,
                   const uint8_t **pstr, size_t *psize);
bool ReadTagInt32(Buffer *buf, tag_t tag, int32_t *pval);
bool ReadTagUInt32(Buffer *buf, tag_t tag, uint32_t *pval);
bool ReadTagUInt64(Buffer *buf, tag_t tag, uint64_t *pval);
bool ReadTagEmpty(Buffer *buf, tag_t tag);

// peek at the next tag in the input, but don't consume anything.
// return 0 if the buffer is not at a valid primitive or complex open tag
tag_t PeekOpenTag(Buffer *buf);

// Packet methods. a packet is a binary blob of data with a TAG_UInt32
// prefix indicating the length of the blob (length does not
// include the prefix).

// read in a packet of data from the specified file descriptor.
// the range [ output->base, output->pos > indicates the range of
// data read by this or a previous ReadPacket() operation.
// returns true iff the entire packet was read in; the packet data is
// in the range [ output->base + UINT32_LENGTH, output->pos >
bool ReadPacket(int fd, Buffer *output);

// write a packet of data to the specified file descriptor.
// the range [ input->base, input->pos > indicates the range of
// data written by this or a previous WritePacket() operation.
// returns true iff the entire packet was written.
// the packet data needs to be stored in input starting at
// offset UINT32_LENGTH; the data in
// [ input->base, input->base + UINT32_LENGTH > will be filled in by
// WritePacket before being written.
bool WritePacket(int fd, Buffer *input);

NAMESPACE_XGILL_END
