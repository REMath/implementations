
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

#include "buffer.h"
#include "primitive.h"
#include <zlib.h>
#include <unistd.h>
#include <errno.h>

NAMESPACE_XGILL_BEGIN

#ifdef TRACK_BUFFER_MEMORY
TrackAlloc g_alloc_Buffer("Buffer");
#endif

/////////////////////////////////////////////////////////////////////
// Buffer
/////////////////////////////////////////////////////////////////////

void Buffer::Reset(size_t initial_size)
{
  if (ownsBuffer) {
    if (base != NULL) {
#ifdef TRACK_BUFFER_MEMORY
      track_delete<uint8_t>(*alloc, base);
#else
      delete[] base;
#endif
    }

    if (initial_size != 0) {
      base =
#ifdef TRACK_BUFFER_MEMORY
	track_new<uint8_t>(*alloc, initial_size);
#else
        new uint8_t[initial_size];
#endif
    }
    else {
      base = NULL;
    }
    size = initial_size;
  }

  Reset();
}

void Buffer::Reset()
{
  pos = base;

  if (seen != NULL) {
    delete seen;
    seen = NULL;
  }

  if (seen_rev != NULL) {
    delete seen_rev;
    seen_rev = NULL;
  }

  seen_next = 0;
}

void Buffer::Expand(size_t new_size)
{
  Assert(ownsBuffer);

  Assert(new_size);
  if (new_size < 4096)
    new_size = 4096;

  Assert(new_size > size);
  uint8_t *new_base =
#ifdef TRACK_BUFFER_MEMORY
    track_new<uint8_t>(*alloc, new_size);
#else
    new uint8_t[new_size];
#endif

  if (base != NULL) {
    memcpy(new_base, base, pos - base);
#ifdef TRACK_BUFFER_MEMORY
    track_delete<uint8_t>(*alloc, base);
#else
    delete[] base;
#endif
  }

  uint8_t *new_pos = new_base + (pos - base);
  base = new_base;
  pos  = new_pos;
  size = new_size;
}

bool Buffer::TestSeen(SeenKey v, uint32_t *pid)
{
  if (seen == NULL)
    seen = new SeenTable();

  Vector<uint32_t> *data = seen->Lookup(v, true);
  if (data->Empty()) {
    data->PushBack(seen_next++);
    *pid = seen_next - 1;
    return false;
  }
  else {
    *pid = data->At(0);
    return true;
  }
}

bool Buffer::AddSeenRev(uint32_t id, SeenKey v)
{
  if (seen_rev == NULL)
    seen_rev = new SeenRevTable();

  Vector<SeenKey> *data = seen_rev->Lookup(id, true);
  if (data->Empty()) {
    data->PushBack(v);
    return true;
  }
  else {
    return false;
  }
}

bool Buffer::TestSeenRev(uint32_t id, SeenKey *pv)
{
  if (seen_rev == NULL)
    return false;

  Vector<SeenKey> *data = seen_rev->Lookup(id, false);
  if (data == NULL || data->Empty())
    return false;
  *pv = data->At(0);
  return true;
}

/////////////////////////////////////////////////////////////////////
// Utility methods
/////////////////////////////////////////////////////////////////////

// stride to use when consuming an input stream.
#define BUFFER_STREAM_STRIDE 1000

void ReadInStream(InStream &in, Buffer *buf)
{
  while (!in.IsError() && !in.IsEOF()) {
    buf->Ensure(BUFFER_STREAM_STRIDE);
    size_t count = in.Get(buf->pos, BUFFER_STREAM_STRIDE);
    buf->pos += count;
    if (count < BUFFER_STREAM_STRIDE)
      break;
  }

  if (buf->pos == buf->base || *(buf->pos - 1)) {
    buf->Ensure(1);
    *buf->pos = 0;
    buf->pos++;
  }
}

void SplitBufferStrings(Buffer *buf, char tok, Vector<char*> *strings)
{
  // NULL terminate the buffer contents.
  buf->Ensure(1);
  *buf->pos = 0;

  char *pos = (char*) buf->base;
  while (true) {
    char *end_pos = strchr(pos, tok);
    if (end_pos == NULL) {
      if (strlen(pos) > 0)
        strings->PushBack(pos);
      break;
    }

    // NULL terminate the string at pos by overwriting the token.
    *end_pos = 0;

    strings->PushBack(pos);
    pos = end_pos + 1;
  }
}

// compressed buffers include an 8 byte header followed by data compressed
// with the zlib functions. the header layout is as follows:
// 0..3  length of compressed data (excluding header)
// 4..7  length of uncompressed data
// including this header allows us to include multiple segments
// of compressed data in the same buffer.

void UncompressBuffer(Buffer *input, Buffer *output)
{
  Assert(input->base == input->pos);
  Assert(output->base == output->pos);

  uint32_t compressed_size = 0;
  uint32_t uncompressed_size = 0;

  if (!input->HasRemaining(8)) {
    printf("ERROR: UncompressBuffer() input missing header\n");
    Assert(false);
  }

  // read in the header size data
  Read32(input, &compressed_size);
  Read32(input, &uncompressed_size);

  // input does not contain entire compressed buffer
  if (!input->HasRemaining(compressed_size)) {
    printf("ERROR: UncompressBuffer() input malformed header\n");
    Assert(false);
  }

  output->Ensure(uncompressed_size);
  unsigned long uncompress_len = output->size;

  int ret = uncompress(output->base, &uncompress_len,
                       input->pos, compressed_size);
  if (ret != Z_OK) {
    printf("ERROR: UncompressBuffer() failure: %d\n", ret);
    Assert(false);
  }

  if (uncompress_len != uncompressed_size) {
    printf("ERROR: UncompressBuffer() bad uncompressed size\n");
    Assert(false);
  }

  output->pos = output->base + uncompress_len;
}

void CompressBuffer(Buffer *input, Buffer *output)
{
  Assert(input->base == input->pos);
  Assert(output->base == output->pos);

  output->Ensure(8);

  // write out the header. leave 0 for the compressed size,
  // which we will fill in shortly.
  Write32(output, 0);
  Write32(output, input->size);

  unsigned long uncompressed_len = input->size;
  output->Ensure(compressBound(uncompressed_len));

  // compression level
  int vlevel = 5;

  unsigned long compress_len = output->size;
  int ret = compress2(output->pos, &compress_len,
                      input->base, uncompressed_len,
                      vlevel);
  if (ret != Z_OK) {
    printf("ERROR: CompressBuffer() failure: %d\n", ret);
    Assert(false);
  }

  // write the compressed size
  output->pos = output->base;
  Write32(output, compress_len);

  output->pos = output->base + 8 + compress_len;
}

void UncompressBufferInUse(Buffer *input, Buffer *output)
{
  Buffer read_buf(input->base, input->pos - input->base);
  UncompressBuffer(&read_buf, output);
}

void CompressBufferInUse(Buffer *input, Buffer *output)
{
  Buffer read_buf(input->base, input->pos - input->base);
  CompressBuffer(&read_buf, output);
}

bool ValidString(const uint8_t *data, size_t data_length)
{
  if (data_length == 0)
    return false;
  if (data[data_length - 1] != '\0')
    return false;

  // check the intermediate data is in the printable character
  // range ascii 32 through 126 (' ' through '~').
  const uint8_t *end = &data[data_length - 1];
  for (const uint8_t *v = data; v != end; v++) {
    if (*v < 32 || *v > 126)
      return false;
  }

  return true;
}

#define DECODE_FAIL(where, initial, value)                              \
  do {                                                                  \
    Assert(false);                                                      \
    return value;                                                       \
  } while (0)

// eat an integer constant at the beginning of str, returning the position
// immediately after the constant and storing the integer result
// (if result != NULL). return value is NULL if there was not a valid integer
// constant at the beginning of str. if force_radix != 0 then that radix
// is used. if max_digits != 0 then that maximum number of characters
// is consumed.
inline const char* StringToIntPrefix(const char *str, mpz_t result,
                                     int force_radix, int max_digits)
{
  const char *pos = str;

  bool negative = false;
  if (*pos == '-') {
    negative = true;
    pos++;
  }

  int num_digits = 0;

  int radix = force_radix;
  if (!radix) {
    radix = 10;
    if (*pos == '0') {
      pos++;
      if (*pos == 'x' || *pos == 'X') {
        radix = 16;
        pos++;
      }
      else {
        radix = 8;

        // the first '0' counts as a digit.
        num_digits = 1;
      }
    }
  }

  while (true) {
    if (max_digits && num_digits == max_digits)
      break;

    int digit;
    if (*pos >= '0' && *pos <= '9') {
      digit = *pos - '0';
    }
    else if (radix > 10 && *pos >= 'a' && *pos <= 'f') {
      digit = 10 + (*pos - 'a');
    }
    else if (radix > 10 && *pos >= 'A' && *pos <= 'F') {
      digit = 10 + (*pos - 'A');
    }
    else {
      break;
    }

    // seeing some code used by Chrome that references, e.g. \09. wtf?
    // if (digit >= radix)
    //   DECODE_FAIL("StringToInt", str, NULL);

    mpz_mul_si(result, result, radix);
    mpz_add_ui(result, result, digit);

    pos++;
    num_digits++;
  }

  // number must have at least one digit.
  if (num_digits == 0)
    DECODE_FAIL("StringToInt", str, NULL);

  if (negative)
    mpz_neg(result, result);

  return pos;
}

bool StringToInt(const char *str, mpz_t result)
{
  const char *pos = StringToIntPrefix(str, result, 0, 0);
  if (pos == NULL)
    DECODE_FAIL("StringToInt", str, false);

  // check suffix. allow either i64 (MSVC) or any char sequence from [uUlL].
  if (strcmp(pos, "i64") != 0) {
    while (*pos) {
      if (*pos != 'u' && *pos != 'U' && *pos != 'l' && *pos != 'L')
        DECODE_FAIL("StringToInt", str, false);
      pos++;
    }
  }

  return true;
}

bool StringToInt(const char *str, long *result)
{
  mpz_t mpz;
  mpz_init(mpz);

  bool res = StringToInt(str, mpz);

  if (res && mpz_fits_slong_p(mpz)) {
    *result = mpz_get_si(mpz);
  }
  else {
    res = false;
  }

  if (!res)
    *result = 0;
  mpz_clear(mpz);
  return res;
}

void IntToString(Buffer *buf, const mpz_t value)
{
  size_t needed = mpz_sizeinbase(value, 10) + 2;
  buf->Ensure(needed);

  mpz_get_str((char*) buf->pos, 10, value);

  // advance to the character after the NULL terminator.
  size_t written = strlen((const char*) buf->pos) + 1;
  Assert(written <= needed);

  buf->pos += written;
}

void PrintInt(OutStream &out, const mpz_t value)
{
  static Buffer scratch;

  scratch.Reset();
  IntToString(&scratch, value);
  out << (const char*) scratch.base;
}

const char* GetMinimumInteger(size_t bits, bool sign)
{
  if (!sign)
    return "0";

  switch (bits) {
  case 8:  return "-128";
  case 16: return "-32768";
  case 32: return "-2147483648";
  case 64: return "-9223372036854775808";
  default: Assert(false);
  }
}

const char* GetMaximumInteger(size_t bits, bool sign)
{
  if (sign) {
    switch (bits) {
    case 8:  return "127";
    case 16: return "32767";
    case 32: return "2147483647";
    case 64: return "9223372036854775807";
    default: Assert(false);
    }
  }
  else {
    switch (bits) {
    case 8:  return "255";
    case 16: return "65535";
    case 32: return "4294967295";
    case 64: return "18446744073709551615";
    default: return NULL;
    }
  }
}

// unescape a single character in a character literal or string.
// return value is start of next char in string, or NULL if the unescape
// failed. result receives the unescaped character.
static const char* UnescapeChar(const char *str, char *result)
{
  if (*str == '\\') {
    str++;
    switch (*str) {
    case 'n': *result = '\n'; return str + 1;
    case 't': *result = '\t'; return str + 1;
    case 'v': *result = '\v'; return str + 1;
    case 'b': *result = '\b'; return str + 1;
    case 'r': *result = '\r'; return str + 1;
    case 'f': *result = '\f'; return str + 1;
    case 'a': *result = '\a'; return str + 1;
    case '\\': *result = '\\'; return str + 1;
    case '?':  *result = '\?'; return str + 1;
    case '\'': *result = '\''; return str + 1;
    case '\"': *result = '\"'; return str + 1;

    // hexidecimal constant. these can have any number of digits.
    // we don't check the bounds of the resulting character,
    // as we can't distinguish regular characters from wide characters here.
    case 'x':
    case 'X':
    case 'u':
    case 'U': {
      mpz_t value;
      mpz_init(value);
      const char *pos = StringToIntPrefix(str + 1, value, 16, 0);

      *result = (char) mpz_get_si(value);
      mpz_clear(value);
      return pos;  // may be NULL
    }

    // octal constant. these can have at most 3 digits.
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7': {
      mpz_t value;
      mpz_init(value);
      const char *pos = StringToIntPrefix(str, value, 8, 3);

      if (mpz_cmp_si(value, 0) < 0 || mpz_cmp_si(value, 256) >= 0) {
        mpz_clear(value);
        DECODE_FAIL("UnescapeChar", str, NULL);
      }

      *result = (char) mpz_get_si(value);
      mpz_clear(value);
      return pos;  // may be NULL
    }

    default:
      DECODE_FAIL("UnescapeChar", str, NULL);
    }
  }
  else {
    *result = *str;
    return str + 1;
  }
}

bool UnescapeCharLiteral(const char *str, char *result)
{
  const char *pos = str;

  // just skip a leading 'L' for wide character constants for now.
  if (*pos == 'L')
    pos++;

  if (*pos++ != '\'')
    DECODE_FAIL("UnescapeChar", str, false);

  pos = UnescapeChar(pos, result);
  if (!pos)
    DECODE_FAIL("UnescapeChar", str, false);

  // decode multicharacter literals by throwing away all but the last char.
  while (*pos != '\'') {
    pos = UnescapeChar(pos, result);
    if (!pos)
      DECODE_FAIL("UnescapeChar", str, false);
  }

  if (*pos++ != '\'')
    DECODE_FAIL("UnescapeChar", str, false);
  if (*pos != 0)
    DECODE_FAIL("UnescapeChar", str, false);
  return true;
}

bool UnescapeStringLiteral(const char *str, Buffer *result)
{
  Assert(result->pos == result->base);

  const char *pos = str;

  // just skip a leading 'L' for wide character strings for now.
  if (*pos == 'L')
    pos++;

  if (*pos++ != '\"') {

    // check for magic GCC string literals. TODO: have a better way of
    // handling these guys (handling them correctly would be nice).
    if (strcmp(str, "__FUNCTION__") == 0 ||
        strcmp(str, "__PRETTY_FUNCTION__") == 0) {
      result->Append(str, strlen(str) + 1);
      return true;
    }

    DECODE_FAIL("UnescapeString", str, false);
  }
  while (true) {
    if (*pos == '\"') {
      // check to see if there is another quote following this close quote.
      // in this case another string constant was catenated onto the earlier
      // ones, so discard the two quote marks and continue.
      pos++;

      // watch for concatenating wide strings.
      if (*pos == 'L')
        pos++;

      if (*pos == 0) {
        result->Ensure(1);
        *result->pos++ = 0;
        return true;
      }
      else if (*pos == '\"') {
        pos++;
        continue;
      }
      else {
        DECODE_FAIL("UnescapeString", str, false);
      }
    }

    result->Ensure(1);
    char val;
    pos = UnescapeChar(pos, &val);
    if (!pos)
      DECODE_FAIL("UnescapeString", str, false);

    *result->pos++ = (uint8_t) val;
  }
}

char* HtmlUnescape(const char *val)
{
  char *res = new char[strlen(val) + 1];

  const char *pos = val;
  char *new_pos = res;
  while (*pos) {
    switch (*pos) {
    case '&':
      if (strncmp(pos, "&amp;", 5) == 0) {
        pos += 5;
        *new_pos++ = '&';
        break;
      }
      else if (strncmp(pos, "&lt;", 4) == 0) {
        pos += 4;
        *new_pos++ = '<';
        break;
      }
      else if (strncmp(pos, "&gt;", 4) == 0) {
        pos += 4;
        *new_pos++ = '>';
        break;
      }
      // fall through
    default:
      *new_pos++ = *pos++;
    }
  }
  *new_pos = *pos;

  return res;
}

inline char ToHex(uint8_t v)
{
  Assert(v < 16);
  if (v >= 10) return 'a' + (v - 10);
  else return '0' + v;
}

void PrintString(OutStream &out, const uint8_t *str, size_t len)
{
  for (size_t n = 0; n < len; n++) {
    switch ((char) str[n]) {
    case '\n': out << "\\\\n"; break;
    case '\t': out << "\\\\t"; break;
    case '\v': out << "\\\\v"; break;
    case '\b': out << "\\\\b"; break;
    case '\r': out << "\\\\r"; break;
    case '\f': out << "\\\\f"; break;
    case '\a': out << "\\\\a"; break;
    case '\\': out << "\\\\"; break;
    case '\"': out << "\\\""; break;
    default:
      if (str[n] >= 32 && str[n] <= 126)
        out << (char) str[n];
      else
        out << "\\u00" << ToHex(str[n] >> 4) << ToHex(str[n] & 0xf);
    }
  }
}

void PrintPadding(OutStream &out, size_t pad_spaces)
{
  for (size_t n = 0; n < pad_spaces; n++)
    out << ' ';
}

bool PrintTag(OutStream &out, Buffer *buf, int pad_spaces, uint8_t *extent)
{
  int32_t val;
  uint32_t uval;
  uint64_t luval;
  tag_t tag;

  const uint8_t *str_base = NULL;
  size_t str_len = 0;

  Assert(buf->pos <= extent);

  if (ReadString(buf, &str_base, &str_len)) {
    PrintPadding(out, pad_spaces);
    PrintString(out, str_base, str_len);
    out << endl;
  }
  else if (ReadInt32(buf, &val)) {
    PrintPadding(out, pad_spaces);
    out << "I " << val << endl;
  }
  else if (ReadUInt32(buf, &uval)) {
    PrintPadding(out, pad_spaces);
    out << "U " << uval << endl;
  }
  else if (ReadUInt64(buf, &luval)) {
    PrintPadding(out, pad_spaces);
    out << "LU " << luval << endl;
  }
  else if ((tag = PeekOpenTag(buf))) {
    PrintPadding(out, pad_spaces);
    out << "<" << tag << ">" << endl;

    ReadOpenTag(buf, tag);
    while (!ReadCloseTag(buf, tag)) {
      if (buf->pos > extent)
        return true;

      bool res = PrintTag(out, buf, pad_spaces + 1, extent);
      if (!res)
        return false;
    }

    PrintPadding(out, pad_spaces);
    out << "</" << tag << ">" << endl;
  }
  else {
    return false;
  }

  return true;
}

size_t PrintPartialBuffer(OutStream &out, Buffer *buf)
{
  Buffer newbuf(buf->base, buf->size);
  uint8_t *extent = buf->pos;

  bool parsed = PrintTag(out, &newbuf, 0, extent);
  if (!parsed)
    fprintf(logfile, "ERROR: Buffer parse failed");

  return newbuf.pos - newbuf.base;
}

/////////////////////////////////////////////////////////////////////
// Write methods
/////////////////////////////////////////////////////////////////////

void WriteString(Buffer *buf, const uint8_t *str, size_t str_length)
{
  buf->Ensure(2 + 4 + str_length);
  Write16(buf, TAG_String);
  Write32(buf, str_length);
  memcpy(buf->pos, str, str_length);
  buf->pos += str_length;
}

void WriteInt32(Buffer *buf, int32_t val)
{
  buf->Ensure(2 + 4);
  Write16(buf, TAG_Int32);
  Write32(buf, (uint32_t) val);
}

void WriteUInt32(Buffer *buf, uint32_t val)
{
  buf->Ensure(2 + 4);
  Write16(buf, TAG_UInt32);
  Write32(buf, val);
}

void WriteUInt64(Buffer *buf, uint64_t val)
{
  buf->Ensure(2 + 8);
  Write16(buf, TAG_UInt64);
  Write64(buf, val);
}

void WriteOpenTag(Buffer *buf, tag_t tag)
{
  buf->Ensure(2);
  Write16(buf, tag);
}

void WriteCloseTag(Buffer *buf, tag_t tag)
{
  buf->Ensure(2);
  Write16(buf, (tag | 0x0001));
}

void WriteTagString(Buffer *buf, tag_t tag,
                    const uint8_t *str, size_t str_length)
{
  WriteOpenTag(buf, tag);
  WriteString(buf, str, str_length);
  WriteCloseTag(buf, tag);
}

void WriteTagInt32(Buffer *buf, tag_t tag, int32_t val)
{
  WriteOpenTag(buf, tag);
  WriteInt32(buf, val);
  WriteCloseTag(buf, tag);
}

void WriteTagUInt32(Buffer *buf, tag_t tag, uint32_t val)
{
  WriteOpenTag(buf, tag);
  WriteUInt32(buf, val);
  WriteCloseTag(buf, tag);
}

void WriteTagUInt64(Buffer *buf, tag_t tag, uint64_t val)
{
  WriteOpenTag(buf, tag);
  WriteUInt64(buf, val);
  WriteCloseTag(buf, tag);
}

void WriteTagEmpty(Buffer *buf, tag_t tag)
{
  WriteOpenTag(buf, tag);
  WriteCloseTag(buf, tag);
}

/////////////////////////////////////////////////////////////////////
// Read methods
/////////////////////////////////////////////////////////////////////

bool ReadString(Buffer *buf, const uint8_t **pstr, size_t *psize)
{
  if (!buf->HasRemaining(2 + 4))
    return false;

  tag_t tag;
  Read16(buf, &tag);
  if (tag != TAG_String) {
    Rewind(buf, 2);
    return false;
  }

  uint32_t read_length;
  Read32(buf, &read_length);

  if (!buf->HasRemaining(read_length)) {
    Rewind(buf, 2 + 4);
    return false;
  }

  *pstr = buf->pos;
  *psize = read_length;
  buf->pos += read_length;

  return true;
}

bool ReadInt32(Buffer *buf, int32_t *pval)
{
  if (!buf->HasRemaining(2 + 4))
    return false;

  tag_t tag;
  Read16(buf, &tag);
  if (tag != TAG_Int32) {
    Rewind(buf, 2);
    return false;
  }

  Read32(buf, (uint32_t*) pval);
  return true;
}

bool ReadUInt32(Buffer *buf, uint32_t *pval)
{
  if (!buf->HasRemaining(2 + 4))
    return false;

  tag_t tag;
  Read16(buf, &tag);
  if (tag != TAG_UInt32) {
    Rewind(buf, 2);
    return false;
  }

  Read32(buf, pval);
  return true;
}

bool ReadUInt64(Buffer *buf, uint64_t *pval)
{
  if (!buf->HasRemaining(2 + 8))
    return false;

  tag_t tag;
  Read16(buf, &tag);
  if (tag != TAG_UInt64) {
    Rewind(buf, 2);
    return false;
  }

  Read64(buf, pval);
  return true;
}

bool ReadOpenTag(Buffer *buf, tag_t tag)
{
  if (!buf->HasRemaining(2))
    return false;

  tag_t xtag;
  Read16(buf, &xtag);
  if (xtag != tag) {
    Rewind(buf, 2);
    return false;
  }

  return true;
}

bool ReadCloseTag(Buffer *buf, tag_t tag)
{
  if (!buf->HasRemaining(2))
    return false;

  tag_t xtag;
  Read16(buf, &xtag);

  if (xtag != (tag | 0x0001)) {
    Rewind(buf, 2);
    return false;
  }

  return true;
}

bool ReadTagString(Buffer *buf, tag_t tag,
                   const uint8_t **pstr, size_t *psize)
{
  if (!ReadOpenTag(buf, tag))
    return false;
  if (!ReadString(buf, pstr, psize)) {
    Rewind(buf, 2);
    return false;
  }
  if (!ReadCloseTag(buf, tag)) {
    Rewind(buf, 2 + 4 + *psize);
    Rewind(buf, 2);
    return false;
  }
  return true;
}

bool ReadTagInt32(Buffer *buf, tag_t tag, int32_t *pval)
{
  int32_t val;
  if (!ReadOpenTag(buf, tag))
    return false;
  if (!ReadInt32(buf, &val)) {
    Rewind(buf, 2);
    return false;
  }
  if (!ReadCloseTag(buf, tag)) {
    Rewind(buf, 4);
    Rewind(buf, 2);
    return false;
  }
  *pval = val;
  return true;
}

bool ReadTagUInt32(Buffer *buf, tag_t tag, uint32_t *pval)
{
  uint32_t val;
  if (!ReadOpenTag(buf, tag))
    return false;
  if (!ReadUInt32(buf, &val)) {
    Rewind(buf, 2);
    return false;
  }
  if (!ReadCloseTag(buf, tag)) {
    Rewind(buf, 4);
    Rewind(buf, 2);
    return false;
  }
  *pval = val;
  return true;
}

bool ReadTagUInt64(Buffer *buf, tag_t tag, uint64_t *pval)
{
  uint64_t val;
  if (!ReadOpenTag(buf, tag))
    return false;
  if (!ReadUInt64(buf, &val)) {
    Rewind(buf, 2);
    return false;
  }
  if (!ReadCloseTag(buf, tag)) {
    Rewind(buf, 8);
    Rewind(buf, 2);
    return false;
  }
  *pval = val;
  return true;
}

bool ReadTagEmpty(Buffer *buf, tag_t tag)
{
  if (!ReadOpenTag(buf, tag))
    return false;
  if (!ReadCloseTag(buf, tag)) {
    Rewind(buf, 2);
    return false;
  }
  return true;
}

tag_t PeekOpenTag(Buffer *buf)
{
  if (!buf->HasRemaining(2))
    return 0;

  tag_t xtag;
  Read16(buf, &xtag);
  Rewind(buf, 2);

  if ((xtag & 0x0001) != 0)
    return 0;

  return xtag;
}

/////////////////////////////////////////////////////////////////////
// Packet methods
/////////////////////////////////////////////////////////////////////

bool ReadPacket(int fd, Buffer *output)
{
  size_t read_size = output->pos - output->base;

  if (read_size < UINT32_LENGTH) {
    size_t needed = UINT32_LENGTH - read_size;

    output->Ensure(needed);
    ssize_t ret = read(fd, output->pos, needed);

    if (ret == -1) {
      fprintf(logfile, "ERROR: read() failure: %d\n", errno);
      return false;
    }
    output->pos += ret;
  }

  read_size = output->pos - output->base;

  if (read_size < UINT32_LENGTH) {
    // partial read of the length data
    return false;
  }

  uint32_t data_length = 0;

  Buffer length_buf(output->base, UINT32_LENGTH);
  if (!ReadUInt32(&length_buf, &data_length)) {
    fprintf(logfile, "ERROR: Malformed data in PacketRead()\n");
    return false;
  }

  size_t needed = UINT32_LENGTH + data_length - read_size;

  output->Ensure(needed);
  ssize_t ret = read(fd, output->pos, needed);
  if (ret == -1) {
    fprintf(logfile, "ERROR: read() failure: %d\n", errno);
    return false;
  }
  output->pos += ret;

  return (ret == (ssize_t) needed);
}

bool WritePacket(int fd, Buffer *input)
{
  Assert(input->size >= UINT32_LENGTH);
  size_t data_length = input->size - UINT32_LENGTH;

  // fill in the length information in case it isn't already there.
  if (input->pos == input->base) {
    Buffer length_buf(input->base, UINT32_LENGTH);
    WriteUInt32(&length_buf, data_length);
  }

  size_t read_size = input->pos - input->base;
  size_t needed = UINT32_LENGTH + data_length - read_size;

  ssize_t ret = write(fd, input->pos, needed);
  if (ret == -1) {
    fprintf(logfile, "ERROR: write() failure: %d\n", errno);
    return false;
  }
  input->pos += ret;

  return (ret == (ssize_t) needed);
}

NAMESPACE_XGILL_END
