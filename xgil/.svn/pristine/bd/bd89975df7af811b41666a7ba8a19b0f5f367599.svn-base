
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

NAMESPACE_XGILL_USING

const char *USAGE = "xdbkeys [options] dbname.db";

ConfigOption print_stats(CK_Flag, "print-stats", NULL,
                         "just print key statistics");

int main(int argc, const char **argv)
{
  print_stats.Enable();

  Vector<const char*> unspecified;
  bool parsed = Config::Parse(argc, argv, &unspecified);
  if (!parsed || unspecified.Size() != 1) {
    Config::PrintUsage(USAGE);
    return 1;
  }

  const char *file = unspecified[0];

  Xdb *xdb = new Xdb(file, false, false, true);

  if (!xdb->Exists()) {
    delete xdb;
    return 0;
  }

  if (print_stats.IsSpecified()) {
    xdb->PrintStats();
    delete xdb;
    return 0;
  }

  Buffer key;

  for (uint32_t stream = xdb->MinDataStream();
       stream <= xdb->MaxDataStream();
       stream++) {
    key.Reset();
    xdb->LookupKey(stream, &key);

    Assert(ValidString(key.base, key.pos - key.base));
    logout << (const char*) key.base << endl;
  }

  delete xdb;
  return 0;
}
