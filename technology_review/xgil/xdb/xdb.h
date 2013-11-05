
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

// in memory representation and accessing of an XDB database

#include "layout.h"
#include <util/config.h>

NAMESPACE_XGILL_BEGIN

// single XDB database
class Xdb
{
 public:
  // turn off key caching in generated databases. key caching requires that
  // the entire key stream be read in before the database can be used,
  // in exchange for speeding up database queries. key caching is on
  // by default. does not affect databases that are already open.
  static void DisableKeyCache();

 public:
  // make an XDB for the specified file, creating if it does not exist
  // and do_create is set, truncating if it does exist and do_truncate
  // is set. open the database for accessing if it exists.
  Xdb(const char *file, bool do_create, bool do_truncate, bool read_only);

  // flush the Xdb and close its file if necessary, and destroy it.
  ~Xdb();

  // get a path to the underlying file for the database.
  const char* GetFilePath() { return m_file; }

  // return whether the database has encountered an error. if an error has
  // been encountered the only operation that can be performed is delete
  // (which will close the underlying file).
  bool HasError() { return m_has_error; }

  // print statistics about this database to stdout. detailed statistics
  // are available only if key caching is enabled.
  void PrintStats();

  // flush any changes made by this Xdb to disk.
  void Flush();

  // is this database available for accessing?
  bool Exists();

  // create the database if it does not exist, ensuring it can be accessed.
  void Create();

  // truncate the database, clearing all entries.
  void Truncate();

  // for these functions which use buffers, the pos and base fields must
  // be equal, i.e. no data in the buffer has yet been consumed/added.

  // returns whether there is a value associated with the key buffer.
  bool HasKey(Buffer *key);

  // store into the data buffer the value associated with the key buffer.
  // true on success, false on not found.
  bool Find(Buffer *key, Buffer *data);

  // add an association between the values in the key buffer and data buffer.
  // true on success, false on existing key.
  bool Add(Buffer *key, Buffer *data);

  // replace the value associated with the key buffer with the contents
  // of the data buffer. functions as Insert() if there is no value
  // associated with the key.
  void Replace(Buffer *key, Buffer *data);

  // append to the value associated with the key buffer the contents
  // of the data buffer. functions as Insert() if there is no value
  // associated with the key.
  void Append(Buffer *key, Buffer *data);

  // get the range of stream indexes which represent a key/data pair
  // in the database.
  uint32_t MinDataStream()
  {
    Assert(m_fd != -1 && !m_has_error);
    return XDB_DATA_STREAM_BEGIN;
  }
  uint32_t MaxDataStream()
  {
    Assert(m_fd != -1 && !m_has_error);
    return XDB_DATA_STREAM_BEGIN + m_header.data_stream_count - 1;
  }

  // store into the key buffer the key for the data stream with given index.
  void LookupKey(uint32_t stream, Buffer *key);

 public:

  // all in-memory data for a data stream.
  struct StreamInfo
  {
    // identifier of this data stream.
    uint32_t stream;

    // the hash entry read for this stream. out of sync with
    // the file if xdb->m_hash_dirty is set for the xdb and
    // xdb->m_hash_dirty_stream >= stream
    XdbFile::HashStreamEntry hash_entry;

    // the key entry data read for this stream. not used if key caching
    // is disabled. out of sync with the file if key_dirty is set.
    XdbFile::KeyStreamEntry key_entry;
    bool key_dirty;

    StreamInfo();
    ALLOC_OVERRIDE(g_alloc_XdbStreamInfo);
  };

 private:

  // path to the underlying file. owned by this Xdb.
  char *m_file;

  // file descriptor for the underlying file. -1 if the file is not opened
  // (we opened without do_create set and the file doesn't exist).
  int m_fd;

  // whether the underlying file descriptor is read-only.
  bool m_read_only;

  // error encountered while accessing the file.
  bool m_has_error;

  // header data. out of sync with file if m_header_dirty is set.
  // the header's file_size is always in sync with the file.
  XdbFile::FileHeader m_header;
  bool m_header_dirty;

  // all known stream information, indexed by the stream number.
  Vector<StreamInfo*> m_stream_list;

  typedef HashTable<uint32_t,StreamInfo*,UIntHash> XdbHash;

  // fast lookup of information on streams for a given hash value.
  // values in here are shared with m_stream_list.
  XdbHash m_stream_hash;

  // there is some key in the database which is dirty.
  // we don't keep a master list of which keys are dirty so to flush
  // we need to scan all the keys in the database. not used if key caching
  // is disabled.
  bool m_keys_dirty;

  // indicates which portions of the hash stream are dirty (if any).
  // all hash streams >= m_hash_dirty_stream need to be written out to disk.
  // not used if key caching is disabled. hash stream entries only become
  // dirty for newly created entries in the database; if m_hash_dirty is set,
  // m_keys_dirty will also be set.
  bool m_hash_dirty;
  uint32_t m_hash_dirty_stream;

  // whether key caching is enabled on this hash.
  bool m_key_cache_enabled;

 private:

  // compute the hash for the specified key, according to
  // the database's hash method.
  uint32_t do_hash(const uint8_t *key, uint32_t key_length);

  // wrappers for file access functions. set m_error field and print
  // an error message if an error is encountered.
  void do_seek(uint64_t offset);
  void do_truncate(uint64_t size);
  void do_write(void *base, size_t length);
  void do_read(void *base, size_t length);

  // prepare the stream hash and stream list for adding stream information.
  // if there is already data in these it will be cleared
  void InitStreamHash();

  // get a copy of the layout for a stream (which may be data or special).
  XdbFile::StreamLayout GetStreamLayout(uint32_t stream);

  // get a pointer inside stream_hash to the info for a data stream.
  StreamInfo* GetDataStream(uint32_t stream);

  // read in the entire hash or key streams and store in stream_hash.
  void ReadHashStream();
  void ReadKeyStream();

  // read in the key stream entry at the specified offset into the key stream
  // and store it in key_entry.
  void ReadKeyStreamEntry(uint32_t key_offset,
                          XdbFile::KeyStreamEntry *key_entry);

  // look up a data stream layout for the specified key from disk.
  // layout_offset is set to the absolute file position of the layout,
  // and layout is filled in with that layout. true if key was found,
  // false on not found or error.
  bool GetKeyLayout(Buffer *key, uint64_t *layout_offset,
                    XdbFile::StreamLayout *layout);

  // update the next or prev entry (according to update_next)
  // for the source_id stream to refer to target_id. if source_id
  // is zero then either the first or last id in the file will be updated.
  void ChangeStreamLink(uint32_t source_id, uint32_t target_id,
                        bool update_next);

  // fixup the database to mark layout as the last stream.
  void StreamLinkAppend(XdbFile::StreamLayout *layout);

  // update the on-disk length of a key entry to a new length,
  // and reallocate it if necessary. do_copy indicates whether
  // to copy the old data over if a reallocation is performed.
  void UpdateLength(XdbFile::StreamLayout *layout,
                    uint32_t new_length, bool do_copy);

  // insert a new key/data pair into the database
  void InsertEntry(Buffer *key, Buffer *data);
};

NAMESPACE_XGILL_END
