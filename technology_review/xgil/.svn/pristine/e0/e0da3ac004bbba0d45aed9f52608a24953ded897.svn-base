
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

// constructs in the target program baked into the analysis itself.
// this is the centralized location where such information is stored.
// for now these are part of the executable itself, in the future
// they will be read from a configuration file.

#include "modset.h"
#include "summary.h"

// special builtin functions used by annotations.

// function specifying a candidate sufficient condition.
#define ASSERT_CANDIDATE_FUNCTION  "__assert_candidate"

// function returning the upper bound (according to type of the argument)
// of a pointer.
#define UBOUND_FUNCTION "__ubound"

NAMESPACE_XGILL_BEGIN

// whether there is a textual match between the specified decorated
// function name and the 'name' string. we could instead look up the variable
// for the function and get its undecorated name, but this might cause
// problems if we only want to describe one function in a set of
// overlapping names.
inline bool TextNameMatch(Variable *function, const char *name)
{
  const char *function_name = function->GetName()->Value();
  size_t name_len = strlen(name);

  // strip any leading 'static' uniquification from the function name.
  // eat everything up to and including the last colon.

  const char *colon_pos = strchr(function_name, ':');
  if (colon_pos && colon_pos[1] != ':')
    function_name = colon_pos + 1;

  // is name equal to function_name, ignoring any function arguments?
  // account for any cases where the function's decorated name doesn't
  // include argument info, as this can show up for unknown symbols such as
  // with externally loaded annotation functions.

  if (strncmp(function_name, name, name_len) == 0) {
    if (function_name[name_len] == '(')
      return true;
    if (function_name[name_len] == 0)
      return true;
  }

  // otherwise no match.

  return false;
}

// ignored values. TODO: these are stupid hacks.

// ignore indirect calls through methods in the specified type.
bool IgnoreType(String *csu_name);

// ignore the specified field for indirect calls and downstream analysis.
bool IgnoreField(Field *instance_field);

enum IgnoreFunctionKind {
  IGNORE_NONE = 0,

  // don't explore the body of this function.
  IGNORE_DROP,

  // treat calls to this function as unreachable.
  IGNORE_UNREACHABLE,

  // treat calls to this function as returning zero.
  IGNORE_RETURN_ZERO
};

// ignore the specified function according to the specified kind.
IgnoreFunctionKind IgnoreFunction(Variable *function);

// memory allocation.

// return whether the specified function is a primitive memory allocator
// like malloc. if so, stores the expressions for the allocated buffer
// and its size in bytes in the specified arguments; both of these values are
// in the scope of the callee.
bool GetAllocationFunction(Variable *name, Exp **object, Exp **size);

// other functions which are exploration cutoff points like allocators but
// which we do not have an explicit size on (e.g. strchr, strdup).
bool IsCutoffFunction(Variable *name);

// memory copying/setting.

// the specified call edge copies length bytes from source to target.
bool GetCallMemoryCopy(PEdgeCall *edge, Exp **target,
                       Exp **source, Exp **length);

// the specified call edge zeroes length bytes at target.
bool GetCallMemoryZero(PEdgeCall *edge, Exp **target, Exp **length);

// modset/summary generation.

// fill in a modset or summary according to any baked information. these will
// be invoked for every block the modset or summary is queried on;
// there may already be existing information we generated during analysis.
void FillBakedModset(BlockModset *mod);
void FillBakedSummary(BlockSummary *sum);

// GC safety.

// mark a block as not being able to GC.
bool BlockCannotGC(BlockId *id);

// values of the specified type are monitored by a moving GC.
bool TypeIsGCThing(TypeCSU *type);

// any expression which call constructs/destructs a root for.
Exp* CallConstructsGCRoot(PEdgeCall *edge);
Exp* CallDestructsGCRoot(PEdgeCall *edge);

NAMESPACE_XGILL_END
