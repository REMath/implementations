
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

#include <stdio.h>
#include "layout.h"
#include "xdb.h"

NAMESPACE_XGILL_USING

extern "C" {

static Xdb *active_xdb = NULL;

void xdb_open(const char *file)
{
  if (active_xdb)
    delete active_xdb;

  active_xdb = new Xdb(file, false, false, true);

  if (!active_xdb) {
    printf("Could not open XDB %s\n", file);
    abort();
  }
}

int xdb_min_data_stream()
{
  Assert(active_xdb);
  return active_xdb->MinDataStream();
}

int xdb_max_data_stream()
{
  Assert(active_xdb);
  return active_xdb->MaxDataStream();
}

char* xdb_read_key(int stream)
{
  Assert(active_xdb);

  Buffer key;
  active_xdb->LookupKey(stream, &key);

  Assert(ValidString(key.base, key.pos - key.base));
  return strdup((const char *) key.base);
}

char* xdb_read_entry(const char *key)
{
  Assert(active_xdb);

  Buffer bkey((const uint8_t*) key, strlen(key) + 1);
  Buffer cdata;
  Buffer bdata;

  bool success = active_xdb->Find(&bkey, &cdata);
  if (success) {
    UncompressBufferInUse(&cdata, &bdata);
    size_t len = bdata.pos - bdata.base;

    Buffer parse_data(bdata.base, len);
    Buffer result;
    BufferOutStream resultStream(&result);

    PrintJSONBuffer(resultStream, &parse_data);
    return strdup(resultStream.Base());
  }

  return strdup("");
}

void xdb_free(char *data)
{
  free(data);
}

} // extern "C"
