
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

// functions and data for storing and retrieving intermediate language
// data structures.

#include "block.h"
#include <backend/backend_compound.h>

NAMESPACE_XGILL_BEGIN

// database name containing function/initializer CFGs.
#define BODY_DATABASE "src_body.xdb"
#define INIT_DATABASE "src_init.xdb"

// database name containing CSU type definitions.
#define COMP_DATABASE "src_comp.xdb"

// database name containing function/initializer/type annotation CFGs.
#define BODY_ANNOT_DATABASE "annot_body.xdb"
#define INIT_ANNOT_DATABASE "annot_init.xdb"
#define COMP_ANNOT_DATABASE "annot_comp.xdb"

// database to receive contents of files.
#define SOURCE_DATABASE "file_source.xdb"

// database to receive contents of preprocessed files.
#define PREPROC_DATABASE "file_preprocess.xdb"

// hash name for the callgraph edges to sort from. for the frontend.
#define CALLGRAPH_EDGES "callgraph_edges"

// hash name for callgraph nodes containing indirect calls. for frontend.
#define CALLGRAPH_INDIRECT "callgraph_indirect"

// hash names for worklists.
#define WORKLIST_FUNC_HASH "worklist_func_hash"
#define WORKLIST_GLOB_HASH "worklist_glob_hash"
#define WORKLIST_COMP_HASH "worklist_comp_hash"

// hash name used by the block backend for storing the next stage's worklist.
#define WORKLIST_FUNC_NEXT "worklist_func_next"

// cache lookup structures.

typedef HashCache<BlockId*,BlockCFG*,BlockId>    Cache_BlockCFG;
typedef HashCache<String*,BlockCFG*,String>      Cache_Initializer;
typedef HashCache<String*,CompositeCSU*,String>  Cache_CompositeCSU;

// caches for looking up CFGs, initializers, and CSU types.
extern Cache_BlockCFG      BlockCFGCache;
extern Cache_Initializer   InitializerCache;
extern Cache_CompositeCSU  CompositeCSUCache;

typedef HashCache<String*,Vector<BlockCFG*>*,String>  Cache_Annotation;

// caches for looking up annotations on functions, initializers or CSU types.
extern Cache_Annotation  BodyAnnotCache;
extern Cache_Annotation  InitAnnotCache;
extern Cache_Annotation  CompAnnotCache;

// gets a reference on the CFG for id, loading it if necessary.
// NULL if the CFG was not found.
BlockCFG* GetBlockCFG(BlockId *id);

// gets a reference on the annotation CFG for id, loading it if necessary.
// NULL if the CFG was not found, and emits a warning.
BlockCFG* GetAnnotationCFG(BlockId *id);

// add entries to the CFG cache without doing an explicit lookup.
// does *not* consume references on the CFGs.
void BlockCFGCacheAddListWithRefs(const Vector<BlockCFG*> &cfgs);

// clear out CFG and other intermediate language caches.
void ClearBlockCaches();

// read lists of compressed CFGs in transaction operations.
void BlockCFGUncompress(Transaction *t, size_t var_result,
                        Vector<BlockCFG*> *cfgs);

NAMESPACE_XGILL_END
