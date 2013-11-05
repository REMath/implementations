
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

#include "callgraph.h"
#include "escape.h"
#include "mblock.h"
#include "modset.h"
#include "summary.h"

#include <backend/backend.h>

NAMESPACE_XGILL_BEGIN

// functions and structures for storing and retrieving memory analysis
// data. these all use the BACKEND_XDBHASH backend.

// names of databases storing escape information.
#define ESCAPE_EDGE_FORWARD_DATABASE "escape_edge_forward.xdb"
#define ESCAPE_EDGE_BACKWARD_DATABASE "escape_edge_backward.xdb"
#define ESCAPE_ACCESS_DATABASE "escape_access.xdb"

// name of database storing the callees and callers of a function.
#define CALLER_DATABASE "body_caller.xdb"
#define CALLEE_DATABASE "body_callee.xdb"

// name of database storing per-function/initializer memory information.
#define MEMORY_DATABASE "body_memory.xdb"

// name of database storing per-function modset information.
#define MODSET_DATABASE "body_modset.xdb"

// name of database storing per-function analysis summaries.
#define SUMMARY_DATABASE "body_summary.xdb"

// clear the memory, modset and other caches from the memory representation.
void ClearMemoryCaches();

// memory information caches.

typedef HashCache<BlockId*,BlockMemory*,BlockId> Cache_BlockMemory;
typedef HashCache<BlockId*,BlockModset*,BlockId> Cache_BlockModset;
typedef HashCache<BlockId*,BlockSummary*,BlockId> Cache_BlockSummary;

extern Cache_BlockMemory BlockMemoryCache;
extern Cache_BlockModset BlockModsetCache;
extern Cache_BlockSummary BlockSummaryCache;

// add entries to the caches without doing an explicit lookup.
void BlockMemoryCacheAddList(const Vector<BlockMemory*> &mcfgs);
void BlockModsetCacheAddList(const Vector<BlockModset*> &mods);
void BlockSummaryCacheAddList(const Vector<BlockSummary*> &sums);

// get a reference on the data for the specified ID. for unknown/failed IDs
// the memory will be NULL and modset/summary will be non-NULL but empty
// (except for any baked information).
BlockMemory* GetBlockMemory(BlockId *id);
BlockModset* GetBlockModset(BlockId *id);
BlockSummary* GetBlockSummary(BlockId *id);

// escape information caches.

// get the key in an escape edge or access database which stores data for lt.
String* GetTraceKey(Trace *trace);

typedef HashCache<Trace*,EscapeEdgeSet*,Trace> Cache_EscapeEdgeSet;
typedef HashCache<Trace*,EscapeAccessSet*,Trace> Cache_EscapeAccessSet;
typedef HashCache<Variable*,CallEdgeSet*,Variable> Cache_CallEdgeSet;

extern Cache_EscapeEdgeSet EscapeForwardCache;
extern Cache_EscapeEdgeSet EscapeBackwardCache;
extern Cache_EscapeAccessSet EscapeAccessCache;

extern Cache_CallEdgeSet CalleeCache;
extern Cache_CallEdgeSet CallerCache;

// lists which receive generated escape and callgraph information.
extern HashTable<Trace*,EscapeEdgeSet*,Trace> g_pending_escape_forward;
extern HashTable<Trace*,EscapeEdgeSet*,Trace> g_pending_escape_backward;
extern HashTable<Trace*,EscapeAccessSet*,Trace> g_pending_escape_accesses;
extern HashTable<Variable*,CallEdgeSet*,Variable> g_pending_callees;
extern HashTable<Variable*,CallEdgeSet*,Variable> g_pending_callers;

// write out any pending escape/callgraph data.
void WritePendingEscape();

// memory cache utility.

// read/write lists of compressed memory info in transaction operations.
TOperandString* BlockMemoryCompress(Transaction *t,
                                    const Vector<BlockMemory*> &mcfgs);
void BlockMemoryUncompress(Transaction *t, size_t var_result,
                           Vector<BlockMemory*> *mcfgs);

// read/write lists of compressed modsets in transaction operations.
TOperandString* BlockModsetCompress(Transaction *t,
                                    const Vector<BlockModset*> &mods);
void BlockModsetUncompress(Transaction *t, TOperandString *op_data,
                           Vector<BlockModset*> *mods);

// read/write lists of compressed summaries in transaction operations.
TOperandString* BlockSummaryCompress(Transaction *t,
                                     const Vector<BlockSummary*> &sums);
void BlockSummaryUncompress(Transaction *t, TOperandString *op_data,
                            Vector<BlockSummary*> *sums);

NAMESPACE_XGILL_END
