
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

#include "backend_hash.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// backend data
/////////////////////////////////////////////////////////////////////

BACKEND_IMPL_BEGIN

// name and contents for an in-memory hash
struct HashInfo {
  String *name;       // holds a reference
  BackendStringHash *table;

  HashInfo()
    : name(NULL), table(NULL)
  {}
};

// list of all in-memory hashes
Vector<HashInfo> hashes;

void ClearHashes()
{
  for (size_t hind = 0; hind < hashes.Size(); hind++) {
    HashInfo &info = hashes[hind];

    if (info.table)
      info.table->Clear();
    delete info.table;
  }
  hashes.Clear();
}

HashInfo& GetHash(const uint8_t *name, bool do_create = true)
{
  String *name_str = String::Make((const char*)name);
  for (size_t hind = 0; hind < hashes.Size(); hind++) {
    HashInfo &info = hashes[hind];

    if (info.name == name_str) {
      // create the hash if we previously did a non-create access.
      if (do_create && info.table == NULL)
        info.table = new BackendStringHash();

      return info;
    }
  }

  BackendStringHash *table = NULL;
  if (do_create)
    table = new BackendStringHash();

  HashInfo info;
  info.name = name_str;
  info.table = table;
  hashes.PushBack(info);

  return hashes.Back();
}

BACKEND_IMPL_END

BackendStringHash* GetNamedHash(const uint8_t *name)
{
  return BACKEND_IMPL::GetHash(name, false).table;
}

/////////////////////////////////////////////////////////////////////
// backend implementations
/////////////////////////////////////////////////////////////////////

BACKEND_IMPL_BEGIN

bool HashExists(Transaction *t, const Vector<TOperand*> &arguments,
                TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, hash_name, hash_length);

  BackendStringHash *hash = GetHash(hash_name, false).table;

  *result = new TOperandBoolean(t, hash != NULL);
  return true;
}

bool HashClear(Transaction *t, const Vector<TOperand*> &arguments,
               TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, hash_name, hash_length);

  HashInfo &info = GetHash(hash_name, true);
  info.table->Clear();

  return true;
}

bool HashIsEmpty(Transaction *t, const Vector<TOperand*> &arguments,
                 TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, hash_name, hash_length);

  BackendStringHash *hash = GetHash(hash_name, true).table;

  *result = new TOperandBoolean(t, hash->IsEmpty());
  return true;
}

bool HashInsertKey(Transaction *t, const Vector<TOperand*> &arguments,
                   TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_STRING(0, hash_name, hash_length);
  BACKEND_ARG_STRING(1, key_data, key_length);

  HashInfo &info = GetHash(hash_name, true);

  String *keystr = String::Make((const char*) key_data);

  if (info.table->Lookup(keystr, false) != NULL)
    return true;

  // force the insertion.
  info.table->Lookup(keystr, true);

  return true;
}

bool HashInsertValue(Transaction *t, const Vector<TOperand*> &arguments,
                     TOperand **result)
{
  BACKEND_ARG_COUNT(3);
  BACKEND_ARG_STRING(0, hash_name, hash_length);
  BACKEND_ARG_STRING(1, key_data, key_length);
  BACKEND_ARG_STRING(2, value_data, value_length);

  HashInfo &info = GetHash(hash_name, true);

  String *keystr = String::Make((const char*) key_data);
  String *valuestr = String::Make((const char*) value_data);

  Vector<String*> *entries = info.table->Lookup(keystr, true);

  if (entries->Contains(valuestr))
    return true;

  entries->PushBack(valuestr);
  return true;
}

bool HashInsertCheck(Transaction *t, const Vector<TOperand*> &arguments,
                     TOperand **result)
{
  BACKEND_ARG_COUNT(3);
  BACKEND_ARG_STRING(0, hash_name, hash_length);
  BACKEND_ARG_STRING(1, key_data, key_length);
  BACKEND_ARG_STRING(2, value_data, value_length);

  HashInfo &info = GetHash(hash_name, true);

  String *keystr = String::Make((const char*) key_data);
  String *valuestr = String::Make((const char*) value_data);

  Vector<String*> *entries = info.table->Lookup(keystr, true);

  bool found_exists = entries->Contains(valuestr);

  if (!found_exists) {
    // add the entry and consume the reference on valuestr.
    entries->PushBack(valuestr);
  }

  TOperandList *list_val = new TOperandList(t);
  list_val->PushOperand(new TOperandBoolean(t, found_exists));

  // add all the entries to the list result.
  for (size_t eind = 0; eind < entries->Size(); eind++) {
    String *ds = entries->At(eind);
    TOperand *val = new TOperandString(t, ds->Value());
    list_val->PushOperand(val);
  }

  *result = list_val;
  return true;
}

bool HashChooseKey(Transaction *t, const Vector<TOperand*> &arguments,
                   TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, hash_name, hash_length);

  BackendStringHash *hash = GetHash(hash_name, true).table;

  if (hash->IsEmpty()) {
    *result = new TOperandString(t, "");
    return true;
  }

  String *key = hash->ChooseKey();

  const char *new_key = t->CloneString(key->Value());
  *result = new TOperandString(t, new_key);
  return true;
}

bool HashIsMember(Transaction *t, const Vector<TOperand*> &arguments,
                  TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_STRING(0, hash_name, hash_length);
  BACKEND_ARG_STRING(1, key_data, key_length);

  BackendStringHash *hash = GetHash(hash_name, true).table;

  String *keystr = String::Make((const char*) key_data);
  Vector<String*> *entries = hash->Lookup(keystr, false);

  *result = new TOperandBoolean(t, entries != NULL);
  return true;
}

bool HashLookup(Transaction *t, const Vector<TOperand*> &arguments,
                TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_STRING(0, hash_name, hash_length);
  BACKEND_ARG_STRING(1, key_data, key_length);

  BackendStringHash *hash = GetHash(hash_name, true).table;

  String *keystr = String::Make((const char*) key_data);
  Vector<String*> *entries = hash->Lookup(keystr, false);

  TOperandList *list = new TOperandList(t);

  if (entries != NULL) {
    for (size_t eind = 0; eind < entries->Size(); eind++) {
      String *value = entries->At(eind);

      const char *new_value = t->CloneString(value->Value());
      list->PushOperand(new TOperandString(t, new_value));
    }
  }

  *result = list;
  return true;
}

bool HashLookupSingle(Transaction *t, const Vector<TOperand*> &arguments,
                      TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_STRING(0, hash_name, hash_length);
  BACKEND_ARG_STRING(1, key_data, key_length);

  BackendStringHash *hash = GetHash(hash_name, true).table;

  String *keystr = String::Make((const char*) key_data);
  Vector<String*> *entries = hash->Lookup(keystr, false);

  if (entries == NULL || entries->Size() != 1) {
    logout << "ERROR: Key must have a single associated value." << endl;
    return false;
  }

  String *value = entries->At(0);

  const char *new_value = t->CloneString(value->Value());
  *result = new TOperandString(t, new_value);
  return true;
}

bool HashRemove(Transaction *t, const Vector<TOperand*> &arguments,
                TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_STRING(0, hash_name, hash_length);
  BACKEND_ARG_STRING(1, key_data, key_length);

  BackendStringHash *hash = GetHash(hash_name, true).table;

  String *keystr = String::Make((const char*) key_data);
  Vector<String*> *entries = hash->Lookup(keystr, false);

  if (entries != NULL)
    hash->Remove(keystr);

  return true;
}

bool HashAllKeys(Transaction *t, const Vector<TOperand*> &arguments,
                 TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, hash_name, hash_length);

  TOperandList *list = new TOperandList(t);

  if (BackendStringHash *hash = GetNamedHash(hash_name)) {
    HashIteratePtr(hash) {
      const char *key = t->CloneString(hash->ItKey()->Value());
      list->PushOperand(new TOperandString(t, key));
    }
  }

  *result = list;
  return true;
}

BACKEND_IMPL_END

/////////////////////////////////////////////////////////////////////
// backend
/////////////////////////////////////////////////////////////////////

static void start_Hash()
{
  BACKEND_REGISTER(HashExists);
  BACKEND_REGISTER(HashClear);
  BACKEND_REGISTER(HashIsEmpty);
  BACKEND_REGISTER(HashInsertKey);
  BACKEND_REGISTER(HashInsertValue);
  BACKEND_REGISTER(HashInsertCheck);
  BACKEND_REGISTER(HashChooseKey);
  BACKEND_REGISTER(HashIsMember);
  BACKEND_REGISTER(HashLookup);
  BACKEND_REGISTER(HashLookupSingle);
  BACKEND_REGISTER(HashRemove);
  BACKEND_REGISTER(HashAllKeys);
}

static void finish_Hash()
{
  BACKEND_IMPL::ClearHashes();
}

TransactionBackend backend_Hash(start_Hash, finish_Hash);

/////////////////////////////////////////////////////////////////////
// backend wrappers
/////////////////////////////////////////////////////////////////////

NAMESPACE_BEGIN(Backend)

TAction* HashExists(Transaction *t,
                    const char *hash_name,
                    size_t var_result)
{
  BACKEND_CALL(HashExists, var_result);
  call->PushArgument(new TOperandString(t, hash_name));
  return call;
}

TAction* HashClear(Transaction *t,
                   const char *hash_name)
{
  BACKEND_CALL(HashClear, 0);
  call->PushArgument(new TOperandString(t, hash_name));
  return call;
}

TAction* HashIsEmpty(Transaction *t,
                     const char *hash_name,
                     size_t var_result)
{
  BACKEND_CALL(HashIsEmpty, var_result);
  call->PushArgument(new TOperandString(t, hash_name));
  return call;
}

TAction* HashInsertKey(Transaction *t,
                       const char *hash_name,
                       TOperand *key)
{
  BACKEND_CALL(HashInsertKey, 0);
  call->PushArgument(new TOperandString(t, hash_name));
  call->PushArgument(key);
  return call;
}

TAction* HashInsertValue(Transaction *t,
                         const char *hash_name,
                         TOperand *key,
                         TOperand *value)
{
  BACKEND_CALL(HashInsertValue, 0);
  call->PushArgument(new TOperandString(t, hash_name));
  call->PushArgument(key);
  call->PushArgument(value);
  return call;
}

TAction* HashInsertCheck(Transaction *t,
                         const char *hash_name,
                         TOperand *key,
                         TOperand *value,
                         size_t list_result)
{
  BACKEND_CALL(HashInsertCheck, list_result);
  call->PushArgument(new TOperandString(t, hash_name));
  call->PushArgument(key);
  call->PushArgument(value);
  return call;
}

TAction* HashChooseKey(Transaction *t,
                       const char *hash_name,
                       size_t var_result)
{
  BACKEND_CALL(HashChooseKey, var_result);
  call->PushArgument(new TOperandString(t, hash_name));
  return call;
}

TAction* HashIsMember(Transaction *t,
                      const char *hash_name,
                      TOperand *key,
                      size_t var_result)
{
  BACKEND_CALL(HashIsMember, var_result);
  call->PushArgument(new TOperandString(t, hash_name));
  call->PushArgument(key);
  return call;
}

TAction* HashLookup(Transaction *t,
                    const char *hash_name,
                    TOperand *key,
                    size_t var_result)
{
  BACKEND_CALL(HashLookup, var_result);
  call->PushArgument(new TOperandString(t, hash_name));
  call->PushArgument(key);
  return call; 
}

TAction* HashLookupSingle(Transaction *t,
                          const char *hash_name,
                          TOperand *key,
                          size_t var_result)
{
  BACKEND_CALL(HashLookupSingle, var_result);
  call->PushArgument(new TOperandString(t, hash_name));
  call->PushArgument(key);
  return call;
}

TAction* HashRemove(Transaction *t,
                    const char *hash_name,
                    TOperand *key)
{
  BACKEND_CALL(HashRemove, 0);
  call->PushArgument(new TOperandString(t, hash_name));
  call->PushArgument(key);
  return call;
}

TAction* HashAllKeys(Transaction *t,
                     const char *hash_name,
                     size_t var_result)
{
  BACKEND_CALL(HashAllKeys, var_result);
  call->PushArgument(new TOperandString(t, hash_name));
  return call;
}

NAMESPACE_END(Backend)

NAMESPACE_XGILL_END
