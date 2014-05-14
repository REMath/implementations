
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

#include "backend_compound.h"

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// backend wrappers
/////////////////////////////////////////////////////////////////////

NAMESPACE_BEGIN(Backend)
NAMESPACE_BEGIN(Compound)

// HashCreateXdbKeys ($hashname, $dbname)
//   $existvar = HashExists($hashname)
//   if !$existvar
//     HashClear($hashname)
//     $keyslist = XdbAllKeys($dbname)
//     foreach $key in $keyslist
//       HashInsertKey($hashname, $key)

TAction* HashCreateXdbKeys(Transaction *t,
                           const char *hash_name,
                           const char *db_name)
{
  size_t existvar = t->MakeVariable();
  size_t keylistvar = t->MakeVariable();
  size_t keyvar = t->MakeVariable();

  TOperand *existarg = new TOperandVariable(t, existvar);
  TOperand *keylistarg = new TOperandVariable(t, keylistvar);
  TOperand *keyarg = new TOperandVariable(t, keyvar);

  TActionIterate *key_iter = new TActionIterate(t, keyvar, keylistarg);
  key_iter->PushAction(HashInsertKey(t, hash_name, keyarg));

  TActionTest *nex_test = new TActionTest(t, existarg, false);
  nex_test->PushAction(HashClear(t, hash_name));
  nex_test->PushAction(XdbAllKeys(t, db_name, keylistvar));
  nex_test->PushAction(key_iter);

  TActionSequence *sequence = new TActionSequence(t);
  sequence->PushAction(HashExists(t, hash_name, existvar));
  sequence->PushAction(nex_test);

  return sequence;
}

// HashPopXdbKey (hashname, dbname)
//   $return_key = HashChooseKey(hashname)
//   $key_empty = StringIsEmpty($body_key)
//   if !$key_empty
//     HashRemove(hashname, $return_key)
//     $return_value = XdbLookup(dbname, $return_key)

TAction* HashPopXdbKey(Transaction *t,
                       const char *hash_name,
                       const char *db_name,
                       size_t key_result,
                       size_t value_result)
{
  TOperand *key_arg = new TOperandVariable(t, key_result);

  TRANSACTION_MAKE_VAR(key_empty);

  TActionSequence *sequence = new TActionSequence(t);
  sequence->PushAction(HashChooseKey(t, hash_name, key_result));
  sequence->PushAction(StringIsEmpty(t, key_arg, key_empty_var));

  TActionTest *non_empty_test = new TActionTest(t, key_empty, false);
  non_empty_test->PushAction(HashRemove(t, hash_name, key_arg));
  non_empty_test->PushAction(XdbLookup(t, db_name, key_arg, value_result));
  sequence->PushAction(non_empty_test);

  return sequence;
}

// HashRunIfEmpty ($hashname, $action)
//  $var = HashIsEmpty($hashname)
//  if $var
//    $action

TAction* HashRunIfEmpty(Transaction *t,
                        const char *hashname,
                        TAction *action)
{
  size_t emptyvar = t->MakeVariable();
  TOperand *emptyarg = new TOperandVariable(t, emptyvar);

  TActionTest *empty_test = new TActionTest(t, emptyarg, true);
  empty_test->PushAction(action);

  TActionSequence *sequence = new TActionSequence(t);
  sequence->PushAction(HashIsEmpty(t, hashname, emptyvar));
  sequence->PushAction(empty_test);

  return sequence;
}

// XdbClearIfNotHash ($dbname, $hashname)
//  $var = HashExists($hashname)
//  if $var
//    XdbClear($dbname)

TAction* XdbClearIfNotHash(Transaction *t,
                           const char *dbname,
                           const char *hashname)
{
  size_t existvar = t->MakeVariable();
  TOperand *existarg = new TOperandVariable(t, existvar);

  TActionTest *nexist_test = new TActionTest(t, existarg, false);
  nexist_test->PushAction(XdbClear(t, dbname));

  TActionSequence *sequence = new TActionSequence(t);
  sequence->PushAction(HashExists(t, hashname, existvar));
  sequence->PushAction(nexist_test);

  return sequence;
}

NAMESPACE_END(Compound)
NAMESPACE_END(Backend)

/////////////////////////////////////////////////////////////////////
// Lookup transactions
/////////////////////////////////////////////////////////////////////

bool DoLookupTransaction(const char *db_name,
                         const char *key_name,
                         Buffer *buf)
{
  // lookups can occur even as some backends are being finished
  // (i.e. the block backend). allow this behavior, which must come
  // before the Xdb backend itself is finished.
  if (TransactionBackend::HasFinishedBackends()) {
    Assert(!IsAnalysisRemote());

    Xdb *xdb = GetDatabase(db_name, false);
    if (!xdb || !xdb->Exists())
      return false;

    String *key = String::Make(key_name);
    return XdbFindUncompressed(xdb, key, buf);
  }

  Transaction *t = new Transaction();

  size_t data_res = t->MakeVariable(true);
  TOperand *key_arg = new TOperandString(t, key_name);
  t->PushAction(Backend::XdbLookup(t, db_name, key_arg, data_res));

  SubmitTransaction(t);

  TOperandString *data_value = t->LookupString(data_res);

  if (data_value->GetDataLength() == 0) {
    delete t;
    return false;
  }
  else {
    TOperandString::Uncompress(data_value, buf);

    delete t;
    return true;
  }
}

NAMESPACE_XGILL_END
