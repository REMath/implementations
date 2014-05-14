
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

// backend for operations on in-memory hashtables.

#include "backend.h"

NAMESPACE_XGILL_BEGIN

extern TransactionBackend backend_Hash;

// holds a reference for each key/value string
typedef HashTable<String*,String*,HashObject> BackendStringHash;

// for use by other backends, get the hash with the specified name,
// or NULL if it does not exist.
BackendStringHash* GetNamedHash(const uint8_t *name);

NAMESPACE_BEGIN(Backend)

// returns whether a hash exists. a hash exists after the first time
// a function (other than this one) refers to it.
TAction* HashExists(Transaction *t,
                    const char *hash_name,
                    size_t var_result);

// clear all entries from a hash.
TAction* HashClear(Transaction *t,
                   const char *hash_name);

// return whether a hash is empty.
TAction* HashIsEmpty(Transaction *t,
                     const char *hash_name,
                     size_t var_result);

// inserts a new key into a hash. has no effect if that key
// is already present in the hash.
TAction* HashInsertKey(Transaction *t,
                       const char *hash_name,
                       TOperand *key);

// insert a value into a hash for the specified key. if there is
// not an entry for the key then one will be created.
// duplicate values for the same key will be ignored.
TAction* HashInsertValue(Transaction *t,
                         const char *hash_name,
                         TOperand *key,
                         TOperand *value);

// insert a value into a hash for the specified key, and get a unique
// string index to associate with that value for that key. Duplicate inserts
// of the same value will get the same index, and inserts of different values
// will get different indexes. list_result is set with a list of the form
// (exists, entry0, entry1, ...), where exists indicates whether there
// was a previous duplicate insert, and 'entry0, entry1, ...' are the entries
// associated with the key, in the order they were inserted (the key just
// inserted will be one of these, but not necessarily the last one).
TAction* HashInsertCheck(Transaction *t,
                         const char *hash_name,
                         TOperand *key,
                         TOperand *value,
                         size_t list_result);

// choose an arbitrary key from a hash. empty string if the hash is empty.
TAction* HashChooseKey(Transaction *t,
                       const char *hash_name,
                       size_t var_result);

// return whether the specified key has an entry in a hash.
TAction* HashIsMember(Transaction *t,
                      const char *hash_name,
                      TOperand *key,
                      size_t var_result);

// return a list of the values inserted for a particular key.
// list is empty if the key does not have an entry in the hash.
TAction* HashLookup(Transaction *t,
                    const char *hash_name,
                    TOperand *key,
                    size_t var_result);

// return the single value inserted for a particular key.
// error if the key does not have an entry, or has 0 or more than 1
// values inserted for it.
TAction* HashLookupSingle(Transaction *t,
                          const char *hash_name,
                          TOperand *key,
                          size_t var_result);

// remove an entry from the hash, along with all values inserted for it.
TAction* HashRemove(Transaction *t,
                    const char *hash_name,
                    TOperand *key);

// return a list of all the keys in a hash.
TAction* HashAllKeys(Transaction *t,
                     const char *hash_name,
                     size_t var_result);

NAMESPACE_END(Backend)

NAMESPACE_XGILL_END
