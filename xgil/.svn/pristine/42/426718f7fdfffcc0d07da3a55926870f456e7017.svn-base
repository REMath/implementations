
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

#include "backend_xdb.h"
#include "backend_util.h"
#include <xdb/xdb.h>

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// backend data
/////////////////////////////////////////////////////////////////////

BACKEND_IMPL_BEGIN

// name and handle for an open database.
struct XdbInfo {
  String *name;       // holds a reference
  Xdb *xdb;

  XdbInfo() : name(NULL), xdb(NULL) {}
};

// list of all opened databases.
Vector<XdbInfo> databases;

// whether the databases have been cleared. no further access can happen.
bool cleared_databases = false;

void ClearDatabases()
{
  cleared_databases = true;
  for (size_t dind = 0; dind < databases.Size(); dind++) {
    const XdbInfo &info = databases[dind];
    if (info.xdb != NULL)
      delete info.xdb;
  }
  databases.Clear();
}

XdbInfo& GetDatabaseInfo(const uint8_t *name, bool do_create)
{
  Assert(!cleared_databases);
  String *name_str = String::Make((const char*)name);
  for (size_t dind = 0; dind < databases.Size(); dind++) {
    if (databases[dind].name == name_str) {
      XdbInfo &info = databases[dind];

      // create the database if we previously did a non-create access.
      if (do_create && !info.xdb->Exists()) {
        info.xdb->Create();
        if (info.xdb->HasError()) {
          logout << "ERROR: Corrupt database " << (const char*) name << endl;
          info.xdb->Truncate();
        }
      }

      return info;
    }
  }

  Xdb *xdb = new Xdb((const char*) name, do_create, false, false);
  if (xdb->HasError()) {
    logout << "ERROR: Corrupt database " << (const char*) name << endl;
    xdb->Truncate();
  }

  XdbInfo info;
  info.name = name_str;
  info.xdb = xdb;
  databases.PushBack(info);

  return databases.Back();
}

BACKEND_IMPL_END

Xdb* GetDatabase(const char *name, bool do_create)
{
  Backend_IMPL::XdbInfo &info =
    Backend_IMPL::GetDatabaseInfo((const uint8_t*) name, do_create);
  return info.xdb;
}

bool XdbFindUncompressed(Xdb *xdb, String *key, Buffer *data)
{
  Buffer key_buf((const uint8_t*) key->Value(), strlen(key->Value()) + 1);

  static Buffer compress_buf;
  bool res = xdb->Find(&key_buf, &compress_buf);

  if (res)
    UncompressBufferInUse(&compress_buf, data);

  compress_buf.Reset();
  return res;
}

void XdbReplaceCompress(Xdb *xdb, String *key, Buffer *data)
{
  Buffer key_buf((const uint8_t*) key->Value(), strlen(key->Value()) + 1);

  static Buffer compress_buf;
  CompressBufferInUse(data, &compress_buf);

  Buffer final_buf(compress_buf.base, compress_buf.pos - compress_buf.base);
  xdb->Replace(&key_buf, &final_buf);

  compress_buf.Reset();
}

/////////////////////////////////////////////////////////////////////
// backend implementations
/////////////////////////////////////////////////////////////////////

BACKEND_IMPL_BEGIN

bool XdbClear(Transaction *t, const Vector<TOperand*> &arguments,
              TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, db_name, db_length);

  XdbInfo &info = GetDatabaseInfo(db_name, false);

  // nothing to do if the database doesn't exist yet
  if (!info.xdb->Exists())
    return true;

  info.xdb->Truncate();
  Assert(!info.xdb->HasError());

  return true;
}

bool XdbReplace(Transaction *t, const Vector<TOperand*> &arguments,
                TOperand **result)
{
  BACKEND_ARG_COUNT(3);
  BACKEND_ARG_STRING(0, db_name, db_length);
  BACKEND_ARG_STRING(1, key_data, key_length);
  BACKEND_ARG_DATA(2, value_data, value_length);

  XdbInfo &info = GetDatabaseInfo(db_name, true);

  Buffer keybuf(key_data, key_length);
  Buffer valuebuf(value_data, value_length);

  info.xdb->Replace(&keybuf, &valuebuf);
  Assert(!info.xdb->HasError());

  return true;
}

bool XdbAppend(Transaction *t, const Vector<TOperand*> &arguments,
               TOperand **result)
{
  BACKEND_ARG_COUNT(3);
  BACKEND_ARG_STRING(0, db_name, db_length);
  BACKEND_ARG_STRING(1, key_data, key_length);
  BACKEND_ARG_DATA(2, value_data, value_length);

  XdbInfo &info = GetDatabaseInfo(db_name, true);

  Buffer keybuf(key_data, key_length);
  Buffer valuebuf(value_data, value_length);

  info.xdb->Append(&keybuf, &valuebuf);
  Assert(!info.xdb->HasError());

  return true;
}

bool XdbLookup(Transaction *t, const Vector<TOperand*> &arguments,
               TOperand **result)
{
  BACKEND_ARG_COUNT(2);
  BACKEND_ARG_STRING(0, db_name, db_length);
  BACKEND_ARG_STRING(1, key_data, key_length);

  XdbInfo &info = GetDatabaseInfo(db_name, false);

  // return empty data if the database doesn't exist
  if (!info.xdb->Exists()) {
    *result = new TOperandString(t, NULL, 0);
    return true;
  }

  Buffer keybuf(key_data, key_length);

  Buffer *valuebuf = new Buffer();
  t->AddBuffer(valuebuf);

  bool success = info.xdb->Find(&keybuf, valuebuf);
  Assert(!info.xdb->HasError());

  if (success) {
    size_t retlen = valuebuf->pos - valuebuf->base;
    if (retlen == 0) {
      logout << "ERROR: Database " << db_name
             << " contains an empty value for " << key_data << endl;
      return false;
    }

    *result = new TOperandString(t, valuebuf->base, retlen);
  }
  else {
    *result = new TOperandString(t, NULL, 0);
  }

  return true;
}

bool XdbAllKeys(Transaction *t, const Vector<TOperand*> &arguments,
                TOperand **result)
{
  BACKEND_ARG_COUNT(1);
  BACKEND_ARG_STRING(0, db_name, db_length);

  XdbInfo &info = GetDatabaseInfo(db_name, false);

  // return an empty list if the database doesn't exist
  if (!info.xdb->Exists()) {
    *result = new TOperandList(t);
    return true;
  }

  TOperandList *list = new TOperandList(t);

  // scratch buffer for the key
  Buffer key;

  // bulk buffer for storing lots of keys. instead of continually
  // reallocating this, when we run out of space just make a new buffer.
  // the buffer will be pretty big to reduce the number of allocations
  // we end up going (we'll still have to do one allocation per key
  // for the TOperandString).
  Buffer *buf = NULL;

  for (uint32_t stream = info.xdb->MinDataStream();
       stream <= info.xdb->MaxDataStream();
       stream++) {
    // reset the scratch buffer and get the next key
    key.Reset();
    info.xdb->LookupKey(stream, &key);
    size_t key_length = key.pos - key.base;

    if (!ValidString(key.base, key_length)) {
      logout << "ERROR: Database contains a key that is not NULL-terminated."
             << endl;
      return false;
    }

    if (buf == NULL || !buf->HasRemaining(key_length)) {
      buf = new Buffer(4096 * 16 + key_length);
      t->AddBuffer(buf);
    }

    list->PushOperand(new TOperandString(t, buf->pos, key_length));
    buf->Append(key.base, key_length);
  }

  *result = list;
  return true;
}

BACKEND_IMPL_END

/////////////////////////////////////////////////////////////////////
// backend
/////////////////////////////////////////////////////////////////////

static void start_Xdb()
{
  BACKEND_REGISTER(XdbClear);
  BACKEND_REGISTER(XdbReplace);
  BACKEND_REGISTER(XdbAppend);
  BACKEND_REGISTER(XdbLookup);
  BACKEND_REGISTER(XdbAllKeys);
}

static void finish_Xdb()
{
  BACKEND_IMPL::ClearDatabases();
}

TransactionBackend backend_Xdb(start_Xdb, finish_Xdb);

/////////////////////////////////////////////////////////////////////
// backend wrappers
/////////////////////////////////////////////////////////////////////

NAMESPACE_BEGIN(Backend)

TAction* XdbClear(Transaction *t,
                  const char *db_name)
{
  BACKEND_CALL(XdbClear, 0);
  call->PushArgument(new TOperandString(t, db_name));
  return call;
}

TAction* XdbReplace(Transaction *t,
                    const char *db_name,
                    TOperand *key,
                    TOperand *value)
{
  BACKEND_CALL(XdbReplace, 0);
  call->PushArgument(new TOperandString(t, db_name));
  call->PushArgument(key);
  call->PushArgument(value);
  return call;
}

TAction* XdbAppend(Transaction *t,
                   const char *db_name,
                   TOperand *key,
                   TOperand *value)
{
  BACKEND_CALL(XdbAppend, 0);
  call->PushArgument(new TOperandString(t, db_name));
  call->PushArgument(key);
  call->PushArgument(value);
  return call;
}

TAction* XdbLookup(Transaction *t,
                   const char *db_name,
                   TOperand *key,
                   size_t var_result)
{
  BACKEND_CALL(XdbLookup, var_result);
  call->PushArgument(new TOperandString(t, db_name));
  call->PushArgument(key);
  return call;
}

TAction* XdbAllKeys(Transaction *t,
                    const char *db_name,
                    size_t var_result)
{
  BACKEND_CALL(XdbAllKeys, var_result);
  call->PushArgument(new TOperandString(t, db_name));
  return call;
}

NAMESPACE_END(Backend)

NAMESPACE_XGILL_END
