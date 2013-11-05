
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

#include "xdb.h"

#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>

// filesystem differences for OSX, which supports large files without
// special handling or functions.
#ifdef HOST_DARWIN
#define O_LARGEFILE 0
#define lseek64 lseek
#define ftruncate64 ftruncate
typedef off_t off64_t;
#endif

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// Xdb static
/////////////////////////////////////////////////////////////////////

static bool g_key_cache_enabled = true;

void Xdb::DisableKeyCache()
{
  g_key_cache_enabled = false;
}

#define DEFAULT_HASH_SIZE  4096
#define DEFAULT_KEY_SIZE   8192

#define set_error()       Assert(false)
#define report_corrupt()  do { m_has_error = true; } while (0)

/////////////////////////////////////////////////////////////////////
// Xdb::StreamInfo
/////////////////////////////////////////////////////////////////////

Xdb::StreamInfo::StreamInfo()
  : stream(0), hash_entry(), key_entry(), key_dirty(false)
{}

/////////////////////////////////////////////////////////////////////
// Xdb
/////////////////////////////////////////////////////////////////////

Xdb::Xdb(const char *file, bool do_create, bool do_truncate, bool read_only)
  : m_file(NULL), m_fd(-1), m_read_only(read_only), m_has_error(false),
    m_header(), m_header_dirty(false),
    m_keys_dirty(false), m_hash_dirty(false), m_hash_dirty_stream(0),
    m_key_cache_enabled(g_key_cache_enabled)
{
  // check for proper suffix.
  if (strlen(file) < 4 || memcmp(file + strlen(file) - 4, ".xdb", 4) != 0)
    printf("WARNING: bad file suffix: expected .xdb, got %s\n", file);

  // make a copy of the filename.
  m_file = new char[strlen(file) + 1];
  strcpy(m_file, file);

  int flags;
  if (m_read_only)
    flags = O_RDONLY | O_LARGEFILE;
  else
    flags = O_RDWR | O_LARGEFILE;

  // open the specified file.
  m_fd = open(m_file, flags, 0666);

  if (m_fd == -1) {
    if (errno == ENOENT) {
      // file does not exist. create it if we're supposed to.
      if (do_create)
        Create();
    }
    else {
      // encountered an error while opening.
      printf("ERROR: open() failure: %s\n", strerror(errno));
      set_error();
    }
  }
  else if (do_truncate) {
    // file exists and we are going to truncate and recreate it.
    Truncate();
  }
  else {
    // file exists and we are going to open it.
    InitStreamHash();

    Buffer header_data(XDB_HEADER_MIN_SIZE);

    // seek to file beginning and read in the header data.
    do_seek(0);
    do_read(header_data.base, XDB_HEADER_MIN_SIZE);

    m_header.Read(&header_data);
    if (!IsValidFileHeader(m_header)) {
      report_corrupt();
      return;
    }

    // read in the hash stream from disk and store in stream_hash.
    ReadHashStream();

    if (m_key_cache_enabled) {
      // read in the key stream from disk and store it in stream_hash.
      ReadKeyStream();
    }
  }
}

Xdb::~Xdb()
{
  if (m_fd != -1) {

    // flush the database only if we didn't encounter some error while
    // processing the database.
    if (!m_has_error)
      Flush();

    int ret = close(m_fd);
    if (ret != 0)
      printf("ERROR: close() failure: %s\n", strerror(errno));

    InitStreamHash();
  }

  if (m_file != NULL)
    delete[] m_file;
}

void Xdb::PrintStats()
{
  Assert(m_fd != -1 && !m_has_error);

  fprintf(logfile, "Xdb statistics:\n");
  fprintf(logfile, "File size: %lu\n", (uint64_t) m_header.file_size);
  fprintf(logfile, "Data streams: %lu\n", (uint64_t) m_header.data_stream_count);

  if (m_key_cache_enabled) {
    uint64_t allocated = XDB_HEADER_MIN_SIZE;
    uint64_t used = XDB_HEADER_MIN_SIZE;

    for (uint32_t stream = 1; stream <= MaxDataStream(); stream++) {
      XdbFile::StreamLayout layout = GetStreamLayout(stream);

      allocated += layout.size;
      used += layout.length;
    }

    fprintf(logfile, "Bytes allocated: %lu (%.2f)\n", allocated,
	    allocated / (float)m_header.file_size);
    fprintf(logfile, "Bytes used: %lu (%.2f)\n", used,
	    used / (float)m_header.file_size);
  }
}

void Xdb::Flush()
{
  Assert(m_fd != -1 && !m_has_error);

  if (m_read_only)
    return;

  if (m_header_dirty) {
    // write the header to disk.

    size_t header_size = m_header.header_size;
    Buffer header_data(header_size);
    m_header.Write(&header_data);

    // write out the entire header
    do_seek(0);
    do_write(header_data.base, header_size);

    // clear dirty bit
    m_header_dirty = false;
  }

  if (m_hash_dirty) {
    // write all dirty hash stream entries to disk.
    // we can do this as one big write.

    uint32_t dirty_count = MaxDataStream() - m_hash_dirty_stream + 1;
    uint32_t dirty_length = dirty_count * XDB_HASH_STREAM_ENTRY_SIZE;

    Buffer hash_buf(dirty_length);
    for (uint32_t stream = m_hash_dirty_stream;
         stream <= MaxDataStream();
         stream++) {
      StreamInfo *info = GetDataStream(stream);
      info->hash_entry.Write(&hash_buf);
    }

    uint32_t hash_offset =
      (m_hash_dirty_stream - XDB_DATA_STREAM_BEGIN)
      * XDB_HASH_STREAM_ENTRY_SIZE;

    Assert(hash_offset + dirty_length == m_header.hash_stream.length);

    // seek and write out all the dirty hash entries
    do_seek(m_header.hash_stream.offset + hash_offset);
    do_write(hash_buf.base, dirty_length);

    // clear dirty bits
    m_hash_dirty = false;
    m_hash_dirty_stream = 0;
  }

  if (m_keys_dirty) {
    // find all dirty keys. we have to scan the entire database.
    // do it in order so that if dirty keys are clustered around one
    // another (e.g. we mostly did new entry inserts), the writes will
    // also be clustered.

    for (uint32_t stream = MinDataStream();
         stream <= MaxDataStream();
         stream++) {
      StreamInfo *info = GetDataStream(stream);
      if (info->key_dirty) {
        // write the key to disk

        uint32_t dirty_length =
          XDB_KEY_STREAM_ENTRY_SIZE(info->key_entry.key_length);
        Buffer key_buf(dirty_length);
        info->key_entry.Write(&key_buf);

        uint32_t key_offset = info->hash_entry.key_offset;
        Assert(key_offset + dirty_length <= m_header.key_stream.length);

        // seek and write out the key entry
        do_seek(m_header.key_stream.offset + key_offset);
        do_write(key_buf.base, dirty_length);

        // clear dirty bit
        info->key_dirty = false;
      }
    }

    // clear overall dirty bit
    m_keys_dirty = false;
  }
}

bool Xdb::Exists()
{
  Assert(!m_has_error);
  return m_fd != -1;
}

void Xdb::Create()
{
  Assert(m_fd == -1 && !m_has_error);
  Assert(!m_read_only);

  m_fd = open(m_file, O_RDWR | O_LARGEFILE | O_CREAT, 0666);
  if (m_fd == -1) {
    if (errno != ENOENT) {
      printf("ERROR: open() failure: %s\n", strerror(errno));
      set_error();
    }
    return;
  }

  // fill in the header with default information.
  InitStreamHash();

  // mark the header as dirty and don't write it out.
  m_header_dirty = true;

  m_header.magic = XDB_MAGIC;
  m_header.version = XDB_VERSION;
  m_header.header_size = XDB_HEADER_MIN_SIZE;
  m_header.file_size =
    XDB_HEADER_MIN_SIZE + DEFAULT_HASH_SIZE + DEFAULT_KEY_SIZE;
  m_header.data_stream_count = 0;
  m_header.hash_method = XDB_HASH_ELF;

  m_header.hash_stream.id = XDB_HASH_STREAM;
  m_header.hash_stream.offset = XDB_HEADER_MIN_SIZE;
  m_header.hash_stream.size = DEFAULT_HASH_SIZE;
  m_header.hash_stream.length = 0;
  m_header.hash_stream.prev_id = 0;
  m_header.hash_stream.next_id = XDB_KEY_STREAM;

  m_header.key_stream.id = XDB_KEY_STREAM;
  m_header.key_stream.offset = XDB_HEADER_MIN_SIZE + DEFAULT_HASH_SIZE;
  m_header.key_stream.size = DEFAULT_KEY_SIZE;
  m_header.key_stream.length = 0;
  m_header.key_stream.prev_id = XDB_HASH_STREAM;
  m_header.key_stream.next_id = 0;

  m_header.first_id = XDB_HASH_STREAM;
  m_header.last_id = XDB_KEY_STREAM;

  // resize the file to match the header's file size
  do_truncate(m_header.file_size);

  Assert(IsValidFileHeader(m_header));
}

void Xdb::Truncate()
{
  Assert(m_fd != -1);
  Assert(!m_read_only);

  // truncating resets the error bit.
  m_has_error = false;

  // truncate the file to empty
  do_truncate(0);

  // reset the stream hash
  InitStreamHash();

  // clear dirty bits
  m_header_dirty = false;
  m_keys_dirty = false;
  m_hash_dirty = false;
  m_hash_dirty_stream = 0;

  // close the file
  int ret = close(m_fd);
  if (ret != 0) {
    printf("ERROR: close() failure: %s\n", strerror(errno));
    set_error();
    return;
  }
  m_fd = -1;

  // recreate the file
  Create();
}

bool Xdb::HasKey(Buffer *key)
{
  Assert(m_fd != -1 && !m_has_error);
  Assert(key->base == key->pos);

  XdbFile::StreamLayout layout;
  return GetKeyLayout(key, NULL, &layout);
}

bool Xdb::Find(Buffer *key, Buffer *data)
{
  Assert(m_fd != -1 && !m_has_error);
  Assert(key->base == key->pos);
  Assert(data->base == data->pos);

  XdbFile::StreamLayout layout;

  bool success = GetKeyLayout(key, NULL, &layout);
  if (!success)
    return false;

  data->Ensure(layout.length);

  // seek and read in the data itself
  do_seek(layout.offset);
  do_read(data->base, layout.length);

  data->pos += layout.length;
  return true;
}

bool Xdb::Add(Buffer *key, Buffer *data)
{
  Assert(m_fd != -1 && !m_has_error);
  Assert(!m_read_only);
  Assert(key->base == key->pos);
  Assert(data->base == data->pos);

  XdbFile::StreamLayout layout;

  bool success = GetKeyLayout(key, NULL, &layout);
  if (success) {
    // existing entry, don't do anything
    return false;
  }
  else {
    if (m_has_error)
      return false;

    // no existing entry, insert a new one
    InsertEntry(key, data);
    return true;
  }
}

void Xdb::Replace(Buffer *key, Buffer *data)
{
  Assert(m_fd != -1 && !m_has_error);
  Assert(!m_read_only);
  Assert(key->base == key->pos);
  Assert(data->base == data->pos);

  uint64_t layout_offset;
  XdbFile::StreamLayout layout;

  bool success = GetKeyLayout(key, &layout_offset, &layout);
  if (success) {
    // existing entry, replace its data

    // update the length and reallocate if necessary
    UpdateLength(&layout, data->size, false);

    // seek and write out the new data
    do_seek(layout.offset);
    do_write(data->base, data->size);

    if (m_key_cache_enabled) {
      m_keys_dirty = true;

      StreamInfo *info = GetDataStream(layout.id);
      info->key_dirty = true;
      info->key_entry.data_stream = layout;
    }
    else {
      Buffer write_buf(XDB_STREAM_LAYOUT_SIZE);
      layout.Write(&write_buf);

      // write out the updated layout
      do_seek(layout_offset);
      do_write(write_buf.base, XDB_STREAM_LAYOUT_SIZE);
    }
  }
  else {
    if (m_has_error)
      return;

    // no existing entry, insert a new one
    InsertEntry(key, data);
  }
}

void Xdb::Append(Buffer *key, Buffer *data)
{
  Assert(m_fd != -1 && !m_has_error);
  Assert(!m_read_only);
  Assert(key->base == key->pos);
  Assert(data->base == data->pos);

  uint64_t layout_offset;
  XdbFile::StreamLayout layout;

  bool success = GetKeyLayout(key, &layout_offset, &layout);
  if (success) {
    // existing entry, append its data

    // update the length and reallocate if necessary
    size_t old_length = layout.length;
    UpdateLength(&layout, old_length + data->size, true);

    // seek and write out the new data
    do_seek(layout.offset + old_length);
    do_write(data->base, data->size);

    if (m_key_cache_enabled) {
      m_keys_dirty = true;

      StreamInfo *info = GetDataStream(layout.id);
      info->key_dirty = true;
      info->key_entry.data_stream = layout;
    }
    else {
      Buffer write_buf(XDB_STREAM_LAYOUT_SIZE);
      layout.Write(&write_buf);

      // write out the updated layout
      do_seek(layout_offset);
      do_write(write_buf.base, XDB_STREAM_LAYOUT_SIZE);
    }
  }
  else {
    if (m_has_error)
      return;

    // no existing entry, insert a new one
    InsertEntry(key, data);
  }
}

void Xdb::LookupKey(uint32_t stream, Buffer *key)
{
  Assert(m_fd != -1 && !m_has_error);
  Assert(key->base == key->pos);

  StreamInfo *info = GetDataStream(stream);
  Assert(info != NULL);

  if (m_key_cache_enabled) {
    key->Append(info->key_entry.key, info->key_entry.key_length);
  }
  else {
    // get the offset into the key stream to use.
    uint32_t key_offset = info->hash_entry.key_offset;

    XdbFile::KeyStreamEntry key_entry;
    ReadKeyStreamEntry(key_offset, &key_entry);

    key->Append(key_entry.key, key_entry.key_length);
    track_delete<uint8_t>(g_alloc_XdbStreamInfoKey, key_entry.key);
  }
}

uint32_t Xdb::do_hash(const uint8_t *data, uint32_t size)
{
  Assert(m_header.hash_method == XDB_HASH_ELF);
  return ELFHash(0, data, size);
}

void Xdb::do_seek(uint64_t offset)
{
  off64_t ret_off = lseek64(m_fd, offset, L_SET);
  if (ret_off != (off64_t) offset) {
    printf("ERROR: lseek64() failed: %s\n", strerror(errno));
    set_error();
  }
}

void Xdb::do_truncate(uint64_t size)
{
  int ret = ftruncate64(m_fd, size);
  if (ret == -1) {
    printf("ERROR: ftruncate64() failed: %s\n", strerror(errno));
    set_error();
  }
}

void Xdb::do_write(void *base, size_t length)
{
  ssize_t ret_size = write(m_fd, base, length);
  if (ret_size != (ssize_t) length) {
    printf("ERROR: write() failed: %s\n", strerror(errno));
    set_error();
  }
}

void Xdb::do_read(void *base, size_t length)
{
  ssize_t ret_size = read(m_fd, base, length);
  if (ret_size != (ssize_t) length) {
    printf("ERROR: read() failed: %s\n", strerror(errno));
    set_error();
  }
}

void Xdb::InitStreamHash()
{
  // clear stream_hash
  m_stream_hash.Clear();

  // release memory for stream_list entries
  for (uint32_t stream = 0; stream < m_stream_list.Size(); stream++) {
    StreamInfo *info = m_stream_list[stream];
    if (info != NULL) {
      if (info->key_entry.key != NULL)
        track_delete<uint8_t>(g_alloc_XdbStreamInfoKey, info->key_entry.key);
      delete info;
    }
  }

  // clear stream_list and pad it back out with NULL for the special streams
  m_stream_list.Clear();
  for (uint32_t stream = 0; stream < MinDataStream(); stream++)
    m_stream_list.PushBack(NULL);
}

XdbFile::StreamLayout Xdb::GetStreamLayout(uint32_t stream)
{
  if (stream == 0 || stream > MaxDataStream())
    return XdbFile::StreamLayout();

  if (stream == XDB_HASH_STREAM)
    return m_header.hash_stream;
  if (stream == XDB_KEY_STREAM)
    return m_header.key_stream;

  StreamInfo *info = m_stream_list[stream];
  Assert(info != NULL);
  return info->key_entry.data_stream;
}

Xdb::StreamInfo* Xdb::GetDataStream(uint32_t stream)
{
  if (stream < MinDataStream() || stream > MaxDataStream())
    return NULL;

  StreamInfo *info = m_stream_list[stream];
  Assert(info != NULL && info->stream == stream);
  return info;
}

void Xdb::ReadHashStream()
{
  size_t hash_length = m_header.hash_stream.length;

  // check for empty database
  if (hash_length == 0)
    return;

  Buffer hash_data(hash_length);

  // seek to the hash stream data and read in the hash stream
  do_seek(m_header.hash_stream.offset);
  do_read(hash_data.base, hash_length);

  for (uint32_t stream = MinDataStream();
       stream <= MaxDataStream();
       stream++) {
    Assert(m_stream_list.Size() == stream);

    XdbFile::HashStreamEntry hash_entry;
    hash_entry.Read(&hash_data);

    // make and fill in a new StreamInfo
    StreamInfo *info = new StreamInfo();
    info->stream = stream;
    info->hash_entry = hash_entry; 

    // add the StreamInfo to the stream hash and stream list
    m_stream_hash.Insert(hash_entry.hash_value, info);
    m_stream_list.PushBack(info);
  }
}

void Xdb::ReadKeyStream()
{
  Assert(m_key_cache_enabled);
  size_t key_length = m_header.key_stream.length;

  // check for empty database
  if (key_length == 0)
    return;

  Buffer key_data(key_length);

  // seek to the key stream data and read in the key stream
  do_seek(m_header.key_stream.offset);
  do_read(key_data.base, key_length);

  while (key_data.pos - key_data.base != (ssize_t) key_data.size) {
    uint32_t key_offset = key_data.pos - key_data.base;

    XdbFile::KeyStreamEntry key;
    key.Read(&key_data);

    if (key.key == NULL) {
      report_corrupt();
      return;
    }

    if (!IsValidStreamLayout(m_header, key.data_stream)) {
      report_corrupt();
      track_delete<uint8_t>(g_alloc_XdbStreamInfoKey, key.key);
      return;
    }

    StreamInfo *info = GetDataStream(key.data_stream.id);
    if (info == NULL) {
      report_corrupt();
      track_delete<uint8_t>(g_alloc_XdbStreamInfoKey, key.key);
      return;
    }

    if (info->hash_entry.key_offset != key_offset ||
        info->key_entry.data_stream.id != 0) {
      report_corrupt();
      track_delete<uint8_t>(g_alloc_XdbStreamInfoKey, key.key);
      return;
    }

    info->key_entry = key;
  }

  // check consistency of the key data wrt no overlapping keys
  // and correct ordering of key list. we can't do this without the
  // entire key stream in memory.

  for (uint32_t stream = 1; stream <= MaxDataStream(); stream++) {
    XdbFile::StreamLayout layout = GetStreamLayout(stream);

    if (layout.prev_id == 0 && layout.next_id == 0) {
      report_corrupt();
      return;
    }

    if (layout.prev_id == 0) {
      if (m_header.first_id != stream) {
        report_corrupt();
        return;
      }
    }
    else {
      XdbFile::StreamLayout prev_layout = GetStreamLayout(layout.prev_id);
      if (prev_layout.next_id != stream) {
        report_corrupt();
        return;
      }
    }

    if (layout.next_id == 0) {
      if (m_header.last_id != stream) {
        report_corrupt();
        return;
      }
    }
    else {
      XdbFile::StreamLayout next_layout = GetStreamLayout(layout.next_id);
      if (next_layout.prev_id != stream) {
        report_corrupt();
        return;
      }

      // check the file-order sortedness of the two entries
      uint64_t next_begin = layout.offset + layout.size;
      if (next_begin > next_layout.offset) {
        report_corrupt();
        return;
      }
    }
  }
}

void Xdb::ReadKeyStreamEntry(uint32_t key_offset,
                             XdbFile::KeyStreamEntry *key_entry)
{
  // get the absolute offset into the file of the key stream offset
  uint64_t offset = m_header.key_stream.offset + key_offset;

  size_t try_size = XDB_KEY_STREAM_TRY_SIZE;
  if (try_size > m_header.key_stream.length - key_offset)
    try_size = m_header.key_stream.length - key_offset;
  Buffer key_entry_data(try_size);

  // seek to the key position and read in the key
  do_seek(offset);
  do_read(key_entry_data.base, try_size);

  key_entry->Read(&key_entry_data);

  // if we did not get the entire key we need to reread it
  if (key_entry->key == NULL) {
    Assert(key_entry->key_length != 0);

    size_t big_size = XDB_KEY_STREAM_ENTRY_SIZE(key_entry->key_length);
    Buffer key_entry_data_big(big_size);
    
    // reseek to the key position and reread the key
    do_seek(offset);
    do_read(key_entry_data_big.base, big_size);

    key_entry->Read(&key_entry_data_big);
    Assert(key_entry->key != NULL);
  }
}

bool Xdb::GetKeyLayout(Buffer *key,
                       uint64_t *layout_offset,
                       XdbFile::StreamLayout *layout)
{
  Assert(m_fd != -1);
  Assert(key->base == key->pos);

  uint32_t hash = do_hash(key->base, key->size);

  Vector<StreamInfo*> *entries = m_stream_hash.Lookup(hash);
  if (entries != NULL) {
    for (size_t eind = 0; eind < entries->Size(); eind++) {
      StreamInfo *info = entries->At(eind);

      // get the offset into the key stream of the info for this stream.
      uint32_t key_offset = info->hash_entry.key_offset;

      XdbFile::KeyStreamEntry key_entry = info->key_entry;
      bool free_key_entry = false;

      if (!m_key_cache_enabled) {
        // have to read in the key entry from disk
        free_key_entry = true;
        ReadKeyStreamEntry(key_offset, &key_entry);
      }

      // check for (unlikely) mismatch with specified key
      if (key_entry.key_length != key->size ||
          memcmp(key_entry.key, key->base, key->size) != 0) {
        if (free_key_entry)
          track_delete<uint8_t>(g_alloc_XdbStreamInfoKey, key_entry.key);
        continue;
      }

      if (free_key_entry)
        track_delete<uint8_t>(g_alloc_XdbStreamInfoKey, key_entry.key);

      // success!

      if (layout_offset) {
        // compute the absolute file offset of the key stream layout
        *layout_offset =
          m_header.key_stream.offset + key_offset
          + XDB_KEY_STREAM_LAYOUT_OFFSET;
      }

      *layout = key_entry.data_stream;
      return true;
    }
  }

  return false;
}

void Xdb::ChangeStreamLink(uint32_t source_id, uint32_t target_id,
                           bool update_next)
{
  if (source_id == 0) {
    // update the first or last ID in the hash to target_id
    m_header_dirty = true;
    if (update_next)
      m_header.first_id = target_id;
    else
      m_header.last_id = target_id;
  }
  else if (source_id == XDB_HASH_STREAM) {
    // update the hash stream to point to target_id
    m_header_dirty = true;
    if (update_next)
      m_header.hash_stream.next_id = target_id;
    else
      m_header.hash_stream.prev_id = target_id;
  }
  else if (source_id == XDB_KEY_STREAM) {
    // update the key stream to point to target_id
    m_header_dirty = true;
    if (update_next)
      m_header.key_stream.next_id = target_id;
    else
      m_header.key_stream.prev_id = target_id;
  }
  else if (m_key_cache_enabled) {
    m_keys_dirty = true;

    StreamInfo *info = GetDataStream(source_id);
    info->key_dirty = true;

    if (update_next)
      info->key_entry.data_stream.next_id = target_id;
    else
      info->key_entry.data_stream.prev_id = target_id;
  }
  else {
    // seek out and overwrite the key layout in the source file
    XdbFile::StreamLayout layout;

    // get the offset into the key stream to use.
    StreamInfo *info = GetDataStream(source_id);
    uint32_t key_offset = info->hash_entry.key_offset;

    Assert(key_offset + XDB_STREAM_LAYOUT_SIZE
           <= m_header.key_stream.length);

    Buffer layout_data(XDB_STREAM_LAYOUT_SIZE);

    // get the absolute offset into the file of the key layout
    uint64_t offset =
      m_header.key_stream.offset + key_offset +
      XDB_KEY_STREAM_LAYOUT_OFFSET;

    // seek to the key position and read in the key layout
    do_seek(offset);
    do_read(layout_data.base, XDB_STREAM_LAYOUT_SIZE);

    layout.Read(&layout_data);

    if (update_next)
      layout.next_id = target_id;
    else
      layout.prev_id = target_id;

    layout_data.Reset();
    layout.Write(&layout_data);

    // reseek and write out the updated key layout
    do_seek(offset);
    do_write(layout_data.base, XDB_STREAM_LAYOUT_SIZE);
  }
}

void Xdb::StreamLinkAppend(XdbFile::StreamLayout *layout)
{
  Assert(layout->prev_id == 0);
  Assert(layout->next_id == 0);
  Assert(m_header.last_id != layout->id);

  layout->prev_id = m_header.last_id;

  m_header_dirty = true;
  m_header.last_id = layout->id;

  ChangeStreamLink(layout->prev_id, layout->id, true);
}

void Xdb::UpdateLength(XdbFile::StreamLayout *layout,
                       uint32_t new_length, bool do_copy)
{
  // update the length in the key stream entry
  uint32_t old_length = layout->length;
  layout->length = new_length;

  if (new_length > layout->size) {
    // we need to allocate new space for the layout.

    uint64_t new_offset = m_header.file_size;
    uint32_t new_size = new_length * 2;
    if (new_size < REALLOCATE_MIN_SIZE)
      new_size = REALLOCATE_MIN_SIZE;

    m_header_dirty = true;
    m_header.file_size += new_size;

    // resize the file to its new length
    do_truncate(m_header.file_size);

    // copy the old data over if needed
    if (do_copy) {
      Buffer old_data(old_length);

      // read in the old data
      do_seek(layout->offset);
      do_read(old_data.base, old_length);

      // copy to the new position at the end of file
      do_seek(new_offset);
      do_write(old_data.base, old_length);
    }

    // update the key entry with new offset and size
    layout->offset = new_offset;
    layout->size = new_size;

    // fixup the linked list entries in the key stream

    // first remove the stream from the list
    ChangeStreamLink(layout->prev_id, layout->next_id, true);
    ChangeStreamLink(layout->next_id, layout->prev_id, false);

    // append the stream to the end of the list
    layout->prev_id = 0;
    layout->next_id = 0;
    StreamLinkAppend(layout);
  }
}

void Xdb::InsertEntry(Buffer *key, Buffer *data)
{
  Assert(m_fd != -1 && !m_has_error);
  Assert(key->base == key->pos);
  Assert(data->base == data->pos);

  m_header_dirty = true;

  // allocate a new stream identifier
  uint32_t new_stream = XDB_DATA_STREAM_BEGIN + m_header.data_stream_count;
  m_header.data_stream_count++;

  // update the length of the hash stream
  uint32_t old_hash_length = m_header.hash_stream.length;
  uint32_t new_hash_length = old_hash_length + XDB_HASH_STREAM_ENTRY_SIZE;
  UpdateLength(&m_header.hash_stream, new_hash_length, true);

  // update the length of the key stream
  uint32_t old_key_length = m_header.key_stream.length;
  uint32_t new_key_length =
    old_key_length + XDB_KEY_STREAM_ENTRY_SIZE(key->size);
  UpdateLength(&m_header.key_stream, new_key_length, true);

  // update the length of the file itself
  uint64_t old_file_size = m_header.file_size;
  m_header.file_size += data->size;
  do_truncate(m_header.file_size);

  // compute the key's hash value
  uint32_t hash = do_hash(key->base, key->size);

  Assert(m_stream_list.Size() == new_stream);

  // make and fill in a new StreamInfo for the entry
  StreamInfo *info = new StreamInfo();
  info->stream = new_stream;
  info->hash_entry.hash_value = hash;
  info->hash_entry.key_offset = old_key_length;

  // add the StreamInfo to the stream hash and stream list
  m_stream_hash.Insert(hash, info);
  m_stream_list.PushBack(info);

  // mark the hash as dirty if necessary
  if (!m_hash_dirty) {
    m_hash_dirty = true;
    m_hash_dirty_stream = new_stream;
  }

  // construct the key stream entry for the new stream
  XdbFile::KeyStreamEntry key_entry;
  key_entry.key = key->base;
  key_entry.key_length = key->size;
  key_entry.data_stream.id = new_stream;
  key_entry.data_stream.offset = old_file_size;
  key_entry.data_stream.size = data->size;
  key_entry.data_stream.length = data->size;
  key_entry.data_stream.prev_id = 0;
  key_entry.data_stream.next_id = 0;

  // append the key stream to the file order list
  StreamLinkAppend(&key_entry.data_stream);

  if (m_key_cache_enabled) {
    m_keys_dirty = true;
    info->key_dirty = true;

    // reallocate the key data we are storing
    key_entry.key = track_new<uint8_t>(g_alloc_XdbStreamInfoKey, key->size);
    memcpy(key_entry.key, key->base, key->size);

    // copy over the key entry
    info->key_entry = key_entry;
  }
  else {
    uint32_t write_length = XDB_KEY_STREAM_ENTRY_SIZE(key->size);
    Buffer key_write_buf(write_length);
    key_entry.Write(&key_write_buf);

    // write out the new key stream entry
    do_seek(m_header.key_stream.offset + old_key_length);
    do_write(key_write_buf.base, write_length);
  }

  // write out the data stream itself
  do_seek(old_file_size);
  do_write(data->base, data->size);
}

NAMESPACE_XGILL_END
