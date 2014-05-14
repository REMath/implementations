
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

#include "baked.h"
#include "mstorage.h"
#include <imlang/storage.h>
#include <backend/backend_block.h>

NAMESPACE_XGILL_BEGIN

// scratch buffer for doing compression.
static Buffer scratch_buf("Buffer_memory_compress");

// maximum capacities for the storage caches.

#define CAP_BLOCK_MEMORY   10000
#define CAP_BLOCK_MODSET   10000
#define CAP_BLOCK_SUMMARY  10000
#define CAP_ESCAPE_EDGE    5000
#define CAP_ESCAPE_ACCESS  5000
#define CAP_CALLGRAPH      20000

void ClearMemoryCaches()
{
  BlockMemoryCache.Clear();
  BlockModsetCache.Clear();
  BlockSummaryCache.Clear();

  EscapeForwardCache.Clear();
  EscapeBackwardCache.Clear();
  EscapeAccessCache.Clear();

  CalleeCache.Clear();
  CallerCache.Clear();
}

String* GetTraceKey(Trace *trace)
{
  static Buffer key_buf;
  key_buf.Reset();

  switch (trace->Kind()) {
  case TK_Func: {
    const char *str = trace->GetFunction()->GetName()->Value();

    key_buf.Append("func:", 5);
    key_buf.Append(str, strlen(str) + 1);
    break;
  }
  case TK_Glob: {
    Variable *var = trace->GetValue()->Root();
    Assert(var != NULL && var->IsGlobal());
    const char *name = var->GetName()->Value();

    key_buf.Append("glob:", 5);
    key_buf.Append(name, strlen(name) + 1);
    break;
  }
  case TK_Comp: {
    const char *comp_name = trace->GetCSUName()->Value();
    key_buf.Append("comp:", 5);
    key_buf.Append(comp_name, strlen(comp_name));

    Field *field = trace->GetValue()->BaseField();
    if (field && !field->IsInstanceFunction()) {
      // regular field offset from the CSU type.
      const char *field_name = field->GetName()->Value();
      key_buf.Append(":", 1);
      key_buf.Append(field_name, strlen(field_name) + 1);
    }
    else {
      // virtual function or base class information on the CSU.
      key_buf.Ensure(1);
      *key_buf.pos = 0;
    }

    break;
  }
  default:
    Assert(false);
  }

  return String::Make((const char*)key_buf.base);
}

/////////////////////////////////////////////////////////////////////
// BlockMemory lookup
/////////////////////////////////////////////////////////////////////

class ExternalLookup_BlockMemory : public Cache_BlockMemory::ExternalLookup
{
  void LookupInsert(Cache_BlockMemory *cache, BlockId *id)
  {
    Assert(id->Kind() == B_Function || id->Kind() == B_Loop ||
           id->Kind() == B_Initializer);

    String *function = id->Function();
    const char *function_name = function->Value();

    if (!DoLookupTransaction(MEMORY_DATABASE, function_name, &scratch_buf)) {
      cache->Insert(id, NULL);
      return;
    }

    Buffer read_buf(scratch_buf.base, scratch_buf.pos - scratch_buf.base);
    Vector<BlockMemory*> mcfg_list;
    BlockMemory::ReadList(&read_buf, &mcfg_list);

    scratch_buf.Reset();
    read_buf.Reset();

    bool found = false;

    for (size_t ind = 0; ind < mcfg_list.Size(); ind++) {
      BlockMemory *mcfg = mcfg_list[ind];
      BlockId *mcfg_id = mcfg->GetId();

      if (id == mcfg_id)
        found = true;

      cache->Insert(mcfg_id, mcfg);
    }

    if (!found)
      cache->Insert(id, NULL);
  }

  void Remove(Cache_BlockMemory *cache, BlockId *id, BlockMemory *mcfg)
  {}
};

ExternalLookup_BlockMemory lookup_BlockMemory;
Cache_BlockMemory BlockMemoryCache(&lookup_BlockMemory, CAP_BLOCK_MEMORY);

void BlockMemoryCacheAddList(const Vector<BlockMemory*> &mcfgs)
{
  for (size_t ind = 0; ind < mcfgs.Size(); ind++) {
    BlockMemory *mcfg = mcfgs[ind];
    BlockId *id = mcfg->GetId();
    BlockMemoryCache.Insert(id, mcfg);
  }
}

BlockMemory* GetBlockMemory(BlockId *id)
{
  BlockMemory *mcfg = BlockMemoryCache.Lookup(id);

  if (mcfg == NULL) {
    BlockMemoryCache.Release(id);
    return NULL;
  }

  BlockCFG *cfg = GetBlockCFG(id);
  if (cfg)
    mcfg->SetCFG(cfg);

  BlockMemoryCache.Release(id);
  return mcfg;
}

/////////////////////////////////////////////////////////////////////
// BlockModset lookup
/////////////////////////////////////////////////////////////////////

class ExternalLookup_BlockModset : public Cache_BlockModset::ExternalLookup
{
  void LookupInsert(Cache_BlockModset *cache, BlockId *id)
  {
    Assert(id->Kind() == B_Function || id->Kind() == B_Loop);
    String *function = id->Function();
    const char *function_name = function->Value();

    if (!DoLookupTransaction(MODSET_DATABASE, function_name, &scratch_buf)) {
     missing:
      // ensure there is always a modset, even if empty.
      BlockModset *bmod = BlockModset::Make(id);
      FillBakedModset(bmod);

      cache->Insert(id, bmod);
      return;
    }

    Buffer read_buf(scratch_buf.base, scratch_buf.pos - scratch_buf.base);
    Vector<BlockModset*> bmod_list;
    BlockModset::ReadList(&read_buf, &bmod_list);

    scratch_buf.Reset();
    read_buf.Reset();

    bool found = false;

    for (size_t ind = 0; ind < bmod_list.Size(); ind++) {
      BlockModset *bmod = bmod_list[ind];
      BlockId *bmod_id = bmod->GetId();

      if (id == bmod_id)
        found = true;

      // augment this modset with any baked information.
      FillBakedModset(bmod);

      cache->Insert(bmod_id, bmod);
    }

    if (!found)
      goto missing;
  }

  void Remove(Cache_BlockModset *cache, BlockId *id, BlockModset *bmod)
  {}
};

ExternalLookup_BlockModset lookup_BlockModset;
Cache_BlockModset BlockModsetCache(&lookup_BlockModset, CAP_BLOCK_MODSET);

void BlockModsetCacheAddList(const Vector<BlockModset*> &mods)
{
  for (size_t ind = 0; ind < mods.Size(); ind++) {
    BlockModset *bmod = mods[ind];
    BlockId *id = bmod->GetId();
    BlockModsetCache.Insert(id, bmod);
  }
}

BlockModset* GetBlockModset(BlockId *id)
{
  BlockModset *bmod = BlockModsetCache.Lookup(id);
  Assert(bmod);

  BlockModsetCache.Release(id);
  return bmod;
}

/////////////////////////////////////////////////////////////////////
// BlockSummary lookup
/////////////////////////////////////////////////////////////////////

class ExternalLookup_BlockSummary : public Cache_BlockSummary::ExternalLookup
{
  void LookupInsert(Cache_BlockSummary *cache, BlockId *id)
  {
    Assert(id->Kind() == B_Function || id->Kind() == B_Loop ||
           id->Kind() == B_Initializer);

    // no stored summaries for initializer blocks yet.
    if (id->Kind() == B_Initializer) {
     missing:
      // ensure there is always a summary, even if empty.
      BlockSummary *sum = BlockSummary::Make(id);
      FillBakedSummary(sum);

      cache->Insert(id, sum);
      return;
    }

    String *function = id->Function();
    const char *function_name = function->Value();

    if (!DoLookupTransaction(SUMMARY_DATABASE, function_name, &scratch_buf))
      goto missing;

    Buffer read_buf(scratch_buf.base, scratch_buf.pos - scratch_buf.base);
    Vector<BlockSummary*> sum_list;
    BlockSummary::ReadList(&read_buf, &sum_list);

    scratch_buf.Reset();
    read_buf.Reset();

    bool found = false;

    for (size_t ind = 0; ind < sum_list.Size(); ind++) {
      BlockSummary *sum = sum_list[ind];
      BlockId *sum_id = sum->GetId();

      if (id == sum_id)
        found = true;

      // augment this summary with any baked information.
      FillBakedSummary(sum);

      cache->Insert(sum_id, sum);
    }

    if (!found)
      goto missing;
  }

  void Remove(Cache_BlockSummary *cache, BlockId *id, BlockSummary *sum)
  {}
};

ExternalLookup_BlockSummary lookup_BlockSummary;
Cache_BlockSummary BlockSummaryCache(&lookup_BlockSummary, CAP_BLOCK_SUMMARY);

void BlockSummaryCacheAddList(const Vector<BlockSummary*> &sums)
{
  for (size_t ind = 0; ind < sums.Size(); ind++) {
    BlockSummary *sum = sums[ind];
    BlockId *id = sum->GetId();
    BlockSummaryCache.Insert(id, sum);
  }
}

BlockSummary* GetBlockSummary(BlockId *id)
{
  BlockSummary *sum = BlockSummaryCache.Lookup(id);
  Assert(sum);

  BlockSummaryCache.Release(id);
  return sum;
}

/////////////////////////////////////////////////////////////////////
// EscapeEdge lookup
/////////////////////////////////////////////////////////////////////

class ExternalLookup_EscapeEdge
  : public Cache_EscapeEdgeSet::ExternalLookup
{
 public:
  const char *m_database;
  ExternalLookup_EscapeEdge(const char *database)
    : m_database(database)
  {}

  void LookupInsert(Cache_EscapeEdgeSet *cache, Trace *trace)
  {
    String *key = GetTraceKey(trace);

    if (!DoLookupTransaction(m_database, key->Value(), &scratch_buf)) {
      cache->Insert(trace, NULL);
      return;
    }

    Buffer read_buf(scratch_buf.base, scratch_buf.pos - scratch_buf.base);
    Vector<EscapeEdgeSet*> eset_list;
    EscapeEdgeSet::ReadList(&read_buf, &eset_list);

    scratch_buf.Reset();
    read_buf.Reset();

    bool found = false;

    for (size_t ind = 0; ind < eset_list.Size(); ind++) {
      EscapeEdgeSet *eset = eset_list[ind];
      Trace *use_trace = eset->GetSource();

      if (use_trace == trace)
        found = true;

      cache->Insert(use_trace, eset);
    }

    if (!found)
      cache->Insert(trace, NULL);
  }

  void Remove(Cache_EscapeEdgeSet *cache, Trace *trace, EscapeEdgeSet *eset)
  {}
};

ExternalLookup_EscapeEdge
  lookup_EscapeForward(ESCAPE_EDGE_FORWARD_DATABASE);
Cache_EscapeEdgeSet
EscapeForwardCache(&lookup_EscapeForward, CAP_ESCAPE_EDGE);

ExternalLookup_EscapeEdge
  lookup_EscapeBackward(ESCAPE_EDGE_BACKWARD_DATABASE);
Cache_EscapeEdgeSet
EscapeBackwardCache(&lookup_EscapeBackward, CAP_ESCAPE_EDGE);

HashTable<Trace*,EscapeEdgeSet*,Trace> g_pending_escape_forward;
HashTable<Trace*,EscapeEdgeSet*,Trace> g_pending_escape_backward;

/////////////////////////////////////////////////////////////////////
// EscapeAccess lookup
/////////////////////////////////////////////////////////////////////

class ExternalLookup_EscapeAccess
  : public Cache_EscapeAccessSet::ExternalLookup
{
  void LookupInsert(Cache_EscapeAccessSet *cache, Trace *trace)
  {
    String *key = GetTraceKey(trace);

    if (!DoLookupTransaction(ESCAPE_ACCESS_DATABASE,
                             key->Value(), &scratch_buf)) {
      cache->Insert(trace, NULL);
      return;
    }

    Buffer read_buf(scratch_buf.base, scratch_buf.pos - scratch_buf.base);
    Vector<EscapeAccessSet*> aset_list;
    EscapeAccessSet::ReadList(&read_buf, &aset_list);

    scratch_buf.Reset();
    read_buf.Reset();

    bool found = false;

    for (size_t ind = 0; ind < aset_list.Size(); ind++) {
      EscapeAccessSet *aset = aset_list[ind];
      Trace *use_trace = aset->GetValue();

      if (use_trace == trace)
        found = true;

      cache->Insert(use_trace, aset);
    }

    if (!found)
      cache->Insert(trace, NULL);
  }

  void Remove(Cache_EscapeAccessSet *cache, Trace *trace, EscapeAccessSet *aset)
  {}
};

ExternalLookup_EscapeAccess lookup_EscapeAccess;
Cache_EscapeAccessSet
EscapeAccessCache(&lookup_EscapeAccess, CAP_ESCAPE_ACCESS);

HashTable<Trace*,EscapeAccessSet*,Trace> g_pending_escape_accesses;

/////////////////////////////////////////////////////////////////////
// CallEdge lookup
/////////////////////////////////////////////////////////////////////

class ExternalLookup_CallEdge : public Cache_CallEdgeSet::ExternalLookup
{
 public:
  const char *m_database;
  ExternalLookup_CallEdge(const char *database)
    : m_database(database)
  {}

  void LookupInsert(Cache_CallEdgeSet *cache, Variable *func)
  {
    if (!DoLookupTransaction(m_database, func->GetName()->Value(), &scratch_buf)) {
      cache->Insert(func, NULL);
      return;
    }

    Buffer read_buf(scratch_buf.base, scratch_buf.pos - scratch_buf.base);
    CallEdgeSet *cset = CallEdgeSet::Read(&read_buf);

    scratch_buf.Reset();
    read_buf.Reset();

    cache->Insert(func, cset);
  }

  void Remove(Cache_CallEdgeSet *cache, Variable *func, CallEdgeSet *cset)
  {}
};

ExternalLookup_CallEdge lookup_Caller(CALLER_DATABASE);
Cache_CallEdgeSet CallerCache(&lookup_Caller, CAP_CALLGRAPH);

ExternalLookup_CallEdge lookup_Callee(CALLEE_DATABASE);
Cache_CallEdgeSet CalleeCache(&lookup_Callee, CAP_CALLGRAPH);

HashTable<Variable*,CallEdgeSet*,Variable> g_pending_callees;
HashTable<Variable*,CallEdgeSet*,Variable> g_pending_callers;

/////////////////////////////////////////////////////////////////////
// Memory data compression
/////////////////////////////////////////////////////////////////////

TOperandString* BlockMemoryCompress(Transaction *t,
                              const Vector<BlockMemory*> &mcfgs)
{
  Buffer *data = new Buffer();
  t->AddBuffer(data);

  BlockMemory::WriteList(&scratch_buf, mcfgs);
  CompressBufferInUse(&scratch_buf, data);
  scratch_buf.Reset();

  return new TOperandString(t, data->base, data->pos - data->base);
}

void BlockMemoryUncompress(Transaction *t, size_t var_result,
                           Vector<BlockMemory*> *mcfgs)
{
  TOperandString *op_data = t->LookupString(var_result);
  if (op_data->GetDataLength() == 0)
    return;

  Buffer read_buf(op_data->GetData(), op_data->GetDataLength());
  UncompressBuffer(&read_buf, &scratch_buf);
  Buffer data(scratch_buf.base, scratch_buf.pos - scratch_buf.base);

  BlockMemory::ReadList(&data, mcfgs);
  scratch_buf.Reset();
}

TOperandString* BlockModsetCompress(Transaction *t,
                                    const Vector<BlockModset*> &mods)
{
  Buffer *data = new Buffer();
  t->AddBuffer(data);

  BlockModset::WriteList(&scratch_buf, mods);
  CompressBufferInUse(&scratch_buf, data);
  scratch_buf.Reset();

  return new TOperandString(t, data->base, data->pos - data->base);
}

void BlockModsetUncompress(Transaction *t, TOperandString *op_data,
                           Vector<BlockModset*> *mods)
{
  if (op_data->GetDataLength() == 0)
    return;

  Buffer read_buf(op_data->GetData(), op_data->GetDataLength());
  UncompressBuffer(&read_buf, &scratch_buf);
  Buffer data(scratch_buf.base, scratch_buf.pos - scratch_buf.base);

  BlockModset::ReadList(&data, mods);
  scratch_buf.Reset();
}

TOperandString* BlockSummaryCompress(Transaction *t,
                                     const Vector<BlockSummary*> &sums)
{
  Buffer *data = new Buffer();
  t->AddBuffer(data);

  BlockSummary::WriteList(&scratch_buf, sums);
  CompressBufferInUse(&scratch_buf, data);
  scratch_buf.Reset();

  return new TOperandString(t, data->base, data->pos - data->base);
}

void BlockSummaryUncompress(Transaction *t, TOperandString *op_data,
                            Vector<BlockSummary*> *sums)
{
  if (op_data->GetDataLength() == 0)
    return;

  Buffer read_buf(op_data->GetData(), op_data->GetDataLength());
  UncompressBuffer(&read_buf, &scratch_buf);
  Buffer data(scratch_buf.base, scratch_buf.pos - scratch_buf.base);

  BlockSummary::ReadList(&data, sums);
  scratch_buf.Reset();
}

static Buffer pending_buf;

static void WritePendingEscapeEdge(Transaction *t, EscapeEdgeSet *eset)
{
  EscapeEdgeSet::Write(&pending_buf, eset);

  if (pending_buf.pos - pending_buf.base > TRANSACTION_DATA_LIMIT) {
    TOperand *list_op = TOperandString::Compress(t, &pending_buf);
    t->PushAction(Backend::BlockWriteList(t, list_op));
    SubmitTransaction(t);
    t->Clear();
    pending_buf.Reset();
  }
}

static void WritePendingEscapeAccess(Transaction *t, EscapeAccessSet *aset)
{
  EscapeAccessSet::Write(&pending_buf, aset);

  if (pending_buf.pos - pending_buf.base > TRANSACTION_DATA_LIMIT) {
    TOperand *list_op = TOperandString::Compress(t, &pending_buf);
    t->PushAction(Backend::BlockWriteList(t, list_op));
    SubmitTransaction(t);
    t->Clear();
    pending_buf.Reset();
  }
}

static void WritePendingCallEdge(Transaction *t, CallEdgeSet *cset)
{
  CallEdgeSet::Write(&pending_buf, cset);

  if (pending_buf.pos - pending_buf.base > TRANSACTION_DATA_LIMIT) {
    TOperand *list_op = TOperandString::Compress(t, &pending_buf);
    t->PushAction(Backend::BlockWriteList(t, list_op));
    SubmitTransaction(t);
    t->Clear();
    pending_buf.Reset();
  }
}

void WritePendingEscape()
{
  Transaction *t = new Transaction();

  HashIterate(g_pending_escape_forward)
    WritePendingEscapeEdge(t, g_pending_escape_forward.ItValueSingle());
  g_pending_escape_forward.Clear();

  HashIterate(g_pending_escape_backward)
    WritePendingEscapeEdge(t, g_pending_escape_backward.ItValueSingle());
  g_pending_escape_backward.Clear();

  HashIterate(g_pending_escape_accesses)
    WritePendingEscapeAccess(t, g_pending_escape_accesses.ItValueSingle());
  g_pending_escape_accesses.Clear();

  HashIterate(g_pending_callees)
    WritePendingCallEdge(t, g_pending_callees.ItValueSingle());
  g_pending_callees.Clear();

  HashIterate(g_pending_callers)
    WritePendingCallEdge(t, g_pending_callers.ItValueSingle());
  g_pending_callers.Clear();

  if (pending_buf.pos != pending_buf.base) {
    TOperand *list_op = TOperandString::Compress(t, &pending_buf);
    t->PushAction(Backend::BlockWriteList(t, list_op));
    SubmitTransaction(t);
    t->Clear();
    pending_buf.Reset();
  }

  delete t;
}

NAMESPACE_XGILL_END
