
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

// backend for performing operations on Xdb databases.

#include "backend.h"
#include <xdb/xdb.h>

NAMESPACE_XGILL_BEGIN

extern TransactionBackend backend_Xdb;

// interface which other backends can use to access databases.
Xdb* GetDatabase(const char *name, bool do_create);

// get the contents of xdb at key and uncompress them into data.
// returns whether the find was successful.
bool XdbFindUncompressed(Xdb *xdb, String *key, Buffer *data);

// compress the in-use portion of data and store it in xdb at key.
void XdbReplaceCompress(Xdb *xdb, String *key, Buffer *data);

NAMESPACE_BEGIN(Backend)

// clear out all entries from a database.
TAction* XdbClear(Transaction *t,
                  const char *db_name);

// replace an entry in a database with the specified value.
TAction* XdbReplace(Transaction *t,
                    const char *db_name,
                    TOperand *key,
                    TOperand *value);

// append an entry in a database with the specified value.
TAction* XdbAppend(Transaction *t,
                   const char *db_name,
                   TOperand *key,
                   TOperand *value);

// return the contents of an entry in a database.
// 0-length string if there is no entry for the specified key.
TAction* XdbLookup(Transaction *t,
                   const char *db_name,
                   TOperand *key,
                   size_t var_result);

// return a list of all the keys in a database.
TAction* XdbAllKeys(Transaction *t,
                    const char *db_name,
                    size_t var_result);

NAMESPACE_END(Backend)

NAMESPACE_XGILL_END
