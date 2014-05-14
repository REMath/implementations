
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
#include <xdb/xdb.h>
#include <util/config.h>

#include <imlang/storage.h>
#include <memory/mstorage.h>

#include <imlang/serial.h>
#include <memory/serial.h>

NAMESPACE_XGILL_USING

const char *USAGE = "xdbfind [options] dbname.db key";

ConfigOption plain_text(CK_Flag, "plain-text", NULL,
                        "print key data as plain text");

ConfigOption raw_tags(CK_Flag, "raw-tags", NULL,
                      "print key data as raw binary tags");

ConfigOption json(CK_Flag, "json", NULL,
		  "print key data as a JSON string");

// read a binary tag value from the specified buffer and get whatever
// hash object it represents from the buffer, returning a reference
// on that object. we will just match against the types of values that
// can appear at the top level of a database entry.
HashObject* ReadSingleValue(Buffer *buf)
{
  switch (PeekOpenTag(buf)) {

  case TAG_BlockCFG:         return BlockCFG::Read(buf);
  case TAG_CompositeCSU:     return CompositeCSU::Read(buf);
  case TAG_EscapeEdgeSet:    return EscapeEdgeSet::Read(buf);
  case TAG_EscapeAccessSet:  return EscapeAccessSet::Read(buf);
  case TAG_CallEdgeSet:      return CallEdgeSet::Read(buf);
  case TAG_BlockModset:      return BlockModset::Read(buf);
  case TAG_BlockSummary:     return BlockSummary::Read(buf);

  // special case: get the CFG too.
  case TAG_BlockMemory: {
    BlockMemory *mcfg = BlockMemory::Read(buf);
    BlockCFG *cfg = GetBlockCFG(mcfg->GetId());
    if (cfg)
      mcfg->SetCFG(cfg);
    return mcfg;
  }

  default:
    logout << "ERROR: Unknown top-level tag in entry: "
           << PeekOpenTag(buf) << endl;
    Assert(false);
  }
}

int main(int argc, const char **argv)
{
  plain_text.Enable();
  raw_tags.Enable();
  json.Enable();

  Vector<const char*> unspecified;
  bool parsed = Config::Parse(argc, argv, &unspecified);
  if (!parsed || unspecified.Size() != 2) {
    Config::PrintUsage(USAGE);
    return 1;
  }

  // we're only doing one access, we don't need the key cache
  Xdb::DisableKeyCache();

  AnalysisPrepare();

  const char *file = unspecified[0];
  const char *key = unspecified[1];

  Xdb *xdb = new Xdb(file, false, false, true);

  if (!xdb->Exists()) {
    delete xdb;
    return 0;
  }

  Buffer bkey((const uint8_t*) key, strlen(key) + 1);
  Buffer cdata;
  Buffer bdata;

  bool success = xdb->Find(&bkey, &cdata);
  if (success) {
    UncompressBufferInUse(&cdata, &bdata);
    size_t len = bdata.pos - bdata.base;

    if (plain_text.IsSpecified()) {
      for (size_t n = 0; n < len; n++)
        logout << (char) bdata.base[n];
      logout << endl;
    }
    else if (raw_tags.IsSpecified()) {
      size_t consumed = 0;
      while (consumed != len) {
        Buffer parse_data(bdata.base + consumed, len - consumed);
        parse_data.pos += len - consumed;

        size_t read_len = PrintPartialBuffer(logout, &parse_data);
        if (read_len == 0)
          break;
        consumed += read_len;
      }
    }
    else if (json.IsSpecified()) {
      Buffer parse_data(bdata.base, len);
      PrintJSONBuffer(logout, &parse_data);
    }
    else {
      Buffer read_buf(bdata.base, len);
      while (read_buf.pos != read_buf.base + len) {
        HashObject *value = ReadSingleValue(&read_buf);
        logout << value << endl;
      }
    }
  }

  delete xdb;

  ClearBlockCaches();
  ClearMemoryCaches();
  AnalysisFinish(0);
}
