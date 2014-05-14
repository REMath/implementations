
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

// general purpose compound actions composed from other backend functions.

#include "backend_util.h"
#include "backend_xdb.h"
#include "backend_hash.h"

NAMESPACE_XGILL_BEGIN

NAMESPACE_BEGIN(Backend)
NAMESPACE_BEGIN(Compound)

// HashCreateXdbKeys creates a hash if it does not exist whose values
// are all the keys in a specified database. this is normally used
// at startup for initializing worklist hashes.

TAction* HashCreateXdbKeys(Transaction *t,
                           const char *hash_name,
                           const char *db_name);

// HashPopXdbKey removes an arbitrary element from a hash,
// and returns that element along with its contents
// in the specified database. this is normally used for removing items
// from worklists whose keys are keys in a database, i.e. those
// initialized with HashCreateXdbKeys.

TAction* HashPopXdbKey(Transaction *t,
                       const char *hash_name,
                       const char *db_name,
                       size_t key_result,
                       size_t value_result);

// run action if the specified hash is empty.
TAction* HashRunIfEmpty(Transaction *t,
                        const char *hash_name,
                        TAction *action);

// clear the database if the specified hash does not exist.
TAction* XdbClearIfNotHash(Transaction *t,
                           const char *db_name,
                           const char *hash_name);

NAMESPACE_END(Compound)
NAMESPACE_END(Backend)

// looks up the specified key in the specified database, returning true
// if the key exists, false otherwise. if the key exists, stores in buf
// the uncompressed contents of the entry.
bool DoLookupTransaction(const char *db_name,
                         const char *key_name,
                         Buffer *buf);

NAMESPACE_XGILL_END
