
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

#include "backend.h"

NAMESPACE_XGILL_BEGIN

// we know about the different available backends in this file.
// previously we had the backends register themselves, but this causes
// problem with static libraries as if the backend is not directly registered
// its code and initializers may be removed from the final binary and it
// will never register itself.

// backends will be started/finished according to the following order.
#define ITERATE_BACKENDS(MACRO)                 \
  /* specialized to imlang, depends on Xdb */   \
  MACRO(backend_Block)                          \
  /* general utility backends */                \
  MACRO(backend_Util)                           \
  MACRO(backend_Xdb)                            \
  MACRO(backend_Hash)

#define REGISTER_BACKEND(BACKEND)  extern TransactionBackend BACKEND;
ITERATE_BACKENDS(REGISTER_BACKEND)
#undef REGISTER_BACKEND

/////////////////////////////////////////////////////////////////////
// TransactionBackend static
/////////////////////////////////////////////////////////////////////

// all functions registered for any backend.
typedef HashTable<String*,TFunction,HashObject> FunctionTable;
static FunctionTable g_functions;

static bool started_backends = false;
static bool finished_backends = false;

void TransactionBackend::StartBackend()
{
  Assert(!started_backends);
  Assert(!finished_backends);
  started_backends = true;

#define START_BACKEND(BACKEND)  (BACKEND).m_start();
  ITERATE_BACKENDS(START_BACKEND)
#undef START_BACKEND
}

void TransactionBackend::FinishBackend()
{
  if (!started_backends)
    return;

  started_backends = false;
  finished_backends = true;

#define FINISH_BACKEND(BACKEND)  if ((BACKEND).m_finish) (BACKEND).m_finish();
  ITERATE_BACKENDS(FINISH_BACKEND)
#undef FINISH_BACKEND

  g_functions.Clear();
}

bool TransactionBackend::HasFinishedBackends()
{
  return finished_backends;
}

bool TransactionBackend::RunFunction(Transaction *t, const char *name,
                                     const Vector<TOperand*> &arguments,
                                     TOperand **result)
{
  Assert(started_backends);

  String *key = String::Make(name);
  Vector<TFunction> *functions = g_functions.Lookup(key);

  if (functions != NULL) {
    Assert(functions->Size() == 1);

    TFunction function = functions->At(0);
    return function(t, arguments, result);
  }

  logout << "ERROR: Unknown backend function: " << name << endl;
  return false;
}

/////////////////////////////////////////////////////////////////////
// TransactionBackend
/////////////////////////////////////////////////////////////////////

void TransactionBackend::RegisterFunction(const char *name,
                                          TFunction function)
{
  String *key = String::Make(name);
  Vector<TFunction> *functions = g_functions.Lookup(key, true);

  if (!functions->Empty()) {
    logout << "ERROR: Duplicate function names in backends: " << name << endl;
    Assert(false);
  }

  functions->PushBack(function);
}

NAMESPACE_XGILL_END
