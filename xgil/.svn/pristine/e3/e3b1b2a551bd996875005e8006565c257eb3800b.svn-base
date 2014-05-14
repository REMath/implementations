
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

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// Ignored values
/////////////////////////////////////////////////////////////////////

// types to outright ignore.
static const char* g_ignore_types[] =
{
  // Firefox types

  // a tremendous number of indirect calls are on the methods in this
  // interface, which can't easily be pruned with a more precise callgraph.
  // these are irrelevant to our analysis, however.
  "nsISupports",

  NULL
};

bool IgnoreType(String *csu_name)
{
  const char **cur_ignore_type = g_ignore_types;
  while (*cur_ignore_type) {
    if (!strcmp(*cur_ignore_type, csu_name->Value()))
      return true;
    cur_ignore_type++;
  }
  return false;
}

// tagged information for a program field.
struct IgnoreFieldInfo
{
  // name of the containing CSU.
  const char *csu_name;

  // name of the field itself. may be NULL to refer to all fields of the CSU.
  const char *field_name;
};

// names of fields to ignore indirect calls on.
static IgnoreFieldInfo g_ignore_field[] =
{
  // Firefox types.

  // next pointer field for an arena allocator whose allocations are performed
  // via macro instantiation. these macros have an alternative path through
  // JS_ArenaAllocate, however, so we still handle them appropriately.
  { "JSArena", "avail" },

  { NULL, NULL }
};

bool IgnoreField(Field *instance_field)
{
  String *csu_name = instance_field->GetCSUType()->GetCSUName();

  String *field_name = instance_field->GetSourceName();
  if (!field_name)
    field_name = instance_field->GetName();

  IgnoreFieldInfo *cur_ignore = g_ignore_field;
  while (cur_ignore->csu_name) {

    if (strcmp(cur_ignore->csu_name, csu_name->Value()) == 0) {
      if (cur_ignore->field_name == NULL)
        return true;

      if (strcmp(cur_ignore->field_name, field_name->Value()) == 0)
        return true;
    }

    cur_ignore++;
  }

  return false;
}

struct IgnoreFunctionInfo
{
  // name of the function.
  const char *name;

  // how to ignore the function.
  IgnoreFunctionKind kind;
};

// names of functions to ignore completely. TODO: we need to specify WHY
// we are ignoring these (should wait on having stub function logic to
// replace this entire file), or we might prune more than we intended.
static IgnoreFunctionInfo g_ignore_function[] =
{
  // Linux functions.

  // ignore ERR_PTR/IS_ERR crap.
  { "ERR_PTR", IGNORE_UNREACHABLE },
  { "PTR_ERR", IGNORE_UNREACHABLE },
  { "IS_ERR", IGNORE_RETURN_ZERO },

  // assuming this always returns a value less than NR_CPUS, though it
  // will return NR_CPUS if there are no online CPUs (probably not possible).
  { "__any_online_cpu", IGNORE_DROP },

  // stupid hacks to get cpus to work.
  { "notifier_call_chain", IGNORE_DROP },
  { "store_online", IGNORE_DROP },

  // Firefox functions.

  // complex functions that break Yices.
  { "s2b", IGNORE_DROP },

  { NULL, IGNORE_NONE }
};

IgnoreFunctionKind IgnoreFunction(Variable *function)
{
  IgnoreFunctionInfo *cur_ignore = g_ignore_function;
  while (cur_ignore->name) {

    if (TextNameMatch(function, cur_ignore->name))
      return cur_ignore->kind;

    cur_ignore++;
  }

  return IGNORE_NONE;
}

/////////////////////////////////////////////////////////////////////
// Allocation functions
/////////////////////////////////////////////////////////////////////

// a malloc-like function, which takes a size argument and returns
// a buffer with that number of bytes.
struct MallocFunctionInfo
{
  // name of the function.
  const char *name;

  // index of the size argument.
  size_t size_arg;
};

// names of all primitive malloc-like functions.
static MallocFunctionInfo g_malloc_functions[] =
{
  // stdlib functions.
  { "malloc", 0 },
  { "realloc", 1 },
  { "void* operator new", 0 },
  { "void* operator new []", 0 },

  // Linux functions.

  { "__alloc_bootmem_core", 1 },
  { "__do_kmalloc", 0 },
  { "__kmalloc", 0 },
  { "kmalloc", 0 },
  { "dma_alloc_coherent", 1 },
  { "__vmalloc_node", 0 },

  // Linux unhandled wrapper functions.

  { "acpi_ut_callocate_and_track", 0 },

  // Firefox functions.

  { "PORT_ArenaAlloc_Util", 1 },
  { "PORT_ArenaGrow_Util", 3 },
  { "PORT_Alloc_Util", 0 },
  { "PL_ArenaAllocate", 1 },
  { "pr_ZoneMalloc", 0 },
  { "pr_ZoneRealloc", 1 },
  { "arena_malloc", 1 },
  { "alloc_small", 2 },
  { "sqlite3Realloc", 1 },
  { "pcacheMalloc", 0 },
  { "nss_zalloc_arena_locked", 1 },
  { "AllocChunk", 1 },
  { "js_NewGCThing", 2 },
  { "JS_ArenaAllocate", 1 },

  // Firefox wrappers. these don't need to be annotated except to break up clusters.
  { "nss_ZAlloc", 1 },
  { "PORT_ZAlloc_Util", 0 },

  { NULL, 0 }
};

// a fixed-size malloc-like function, which returns a buffer of fixed size.
struct FixedMallocFunctionInfo
{
  // name of the function.
  const char *name;

  // size of the buffer returned, in bytes.
  size_t size;
};

// names of all primitive fixed-size malloc functions.
static FixedMallocFunctionInfo g_fixed_malloc_functions[] =
{
  // Linux functions. assuming that when pages are used directly the entire
  // page is accessible.

  { "lowmem_page_address", 4096 },

  { NULL, 0 }
};

// a calloc-like function, which returns a buffer whose size is the sum
// or product of two arguments.
struct CallocFunctionInfo
{
  // name of the function.
  const char *name;

  // operation to apply to the two arguments to get the size.
  BinopKind binop;

  // indexes of the two arguments to combine with the binop.
  size_t size_arg_one;
  size_t size_arg_two;
};

// names of all primitive calloc functions.
static CallocFunctionInfo g_calloc_functions[] =
{
  // stdlib functions.
  { "calloc", B_Mult, 0, 1 },

  // Firefox functions.

  { "JS_ArenaRealloc", B_Plus, 2, 3 },

  { NULL, B_Invalid, 0, 0 }
};

static inline Exp* GetArgumentValue(size_t arg)
{
  Exp *arg_lval = Exp::MakeVar(NULL, VK_Arg, NULL, arg, NULL);
  return Exp::MakeDrf(arg_lval);
}

static inline Exp* GetReturnedValue()
{
  Exp *ret_lval = Exp::MakeVar(NULL, VK_Return, NULL, 0, NULL);
  return Exp::MakeExit(ret_lval, NULL);
}

// get the char* null terminator of exp.
static inline Exp* GetNullTerminate(Exp *exp)
{
  Type *type = Type::MakeInt(1, true);
  Exp *terminate_test = Exp::MakeEmpty();
  ExpInt *terminate_int = Exp::MakeInt(0);

  return Exp::MakeTerminate(exp, type, terminate_test, terminate_int);
}

// get the byte upper bound of exp.
static inline Exp* GetByteUpperBound(Exp *exp)
{
  Type *type = Type::MakeInt(1, true);
  return Exp::MakeBound(BND_Upper, exp, type);
}

// get the byte offset of exp.
static inline Exp* GetByteOffset(Exp *exp)
{
  Type *type = Type::MakeInt(1, true);
  return Exp::MakeBound(BND_Offset, exp, type);
}

bool GetAllocationFunction(Variable *name, Exp **object, Exp **size)
{
  MallocFunctionInfo *cur_malloc = g_malloc_functions;
  while (cur_malloc->name) {
    if (TextNameMatch(name, cur_malloc->name)) {
      *object = GetReturnedValue();
      *size = GetArgumentValue(cur_malloc->size_arg);
      return true;
    }

    cur_malloc++;
  }

  FixedMallocFunctionInfo *cur_fixed = g_fixed_malloc_functions;
  while (cur_fixed->name) {
    if (TextNameMatch(name, cur_fixed->name)) {
      *object = GetReturnedValue();
      *size = Exp::MakeInt(cur_fixed->size);
      return true;
    }

    cur_fixed++; 
  }

  CallocFunctionInfo *cur_calloc = g_calloc_functions;
  while (cur_calloc->name) {
    if (TextNameMatch(name, cur_calloc->name)) {
      Exp *size_one = GetArgumentValue(cur_calloc->size_arg_one);
      Exp *size_two = GetArgumentValue(cur_calloc->size_arg_two);
      *object = GetReturnedValue();
      *size = Exp::MakeBinop(cur_calloc->binop, size_one, size_two);
      return true;
    }

    cur_calloc++;
  }

  return false;
}

// names of additional cutoff functions.
static const char* g_cutoff_functions[] =
{
  // stdlib functions.
  "strdup",
  "strchr",

  // Firefox functions.
  "js_GC",

  NULL
};

bool IsCutoffFunction(Variable *name)
{
  const char **cur_cutoff = g_cutoff_functions;
  while (*cur_cutoff) {
    if (TextNameMatch(name, *cur_cutoff))
      return true;
    cur_cutoff++;
  }

  return false;
}

/////////////////////////////////////////////////////////////////////
// Memory copying functions
/////////////////////////////////////////////////////////////////////

// a memcpy-like function, which copies a number of bytes from one pointer
// to another.
struct MemcpyFunctionInfo
{
  // name of the function.
  const char *name;

  // index of the target, source, and length arguments.
  size_t target_arg;
  size_t source_arg;
  size_t length_arg;
};

static MemcpyFunctionInfo g_memcpy_functions[] =
{
  // stdlib functions.
  { "memcpy", 0, 1, 2 },
  { "strncpy", 0, 1, 2 },  // won't copy past the null; this is close enough.

  { NULL, 0, 0, 0 }
};

// a realloc-like function, which copies bytes from a previously allocated
// buffer to a newly allocated buffer.
struct ReallocFunctionInfo
{
  // name of the function.
  const char *name;

  // index of the base pointer of the old buffer. the number of bytes copied
  // is the upper bound of this pointer. TODO: not modelling realloc case
  // where the buffer shrinks.
  size_t base_arg;
};

static ReallocFunctionInfo g_realloc_functions[] =
{
  // stdlib functions.
  { "realloc", 0 },

  { NULL, 0 }
};

bool GetCallMemoryCopy(PEdgeCall *edge, Exp **target,
                       Exp **source, Exp **length)
{
  Variable *name = edge->GetDirectFunction();

  if (!name)
    return false;

  MemcpyFunctionInfo *cur_memcpy = g_memcpy_functions;
  while (cur_memcpy->name) {
    if (TextNameMatch(name, cur_memcpy->name)) {
      *target = GetArgumentValue(cur_memcpy->target_arg);
      *source = GetArgumentValue(cur_memcpy->source_arg);
      *length = GetArgumentValue(cur_memcpy->length_arg);
      return true;
    }

    cur_memcpy++;
  }

  ReallocFunctionInfo *cur_realloc = g_realloc_functions;
  while (cur_realloc->name) {
    if (TextNameMatch(name, cur_realloc->name)) {
      *target = GetReturnedValue();
      *source = GetArgumentValue(cur_realloc->base_arg);
      *length = GetByteUpperBound(*source);
      return true;
    }

    cur_realloc++;
  }

  return false;
}

/////////////////////////////////////////////////////////////////////
// Memory setting functions
/////////////////////////////////////////////////////////////////////

// a memset-like function, which fills in a number of bytes at one pointer
// with the value specified by another argument.
struct MemsetFunctionInfo
{
  // name of the function.
  const char *name;

  // index of the target, value, and length arguments.
  size_t target_arg;
  size_t value_arg;
  size_t length_arg;
};

static MemsetFunctionInfo g_memset_functions[] =
{
  // stdlib functions.
  { "memset", 0, 1, 2 },

  { NULL, 0, 0, 0 }
};

// names of primitive allocators which zero their result.
static const char* g_zero_allocator_functions[] =
{
  // stdlib functions.
  "calloc",

  // firefox functions.
  "nss_zalloc_arena_locked",
  "nss_ZAlloc",
  "PORT_ZAlloc_Util",

  NULL
};

bool GetCallMemoryZero(PEdgeCall *edge, Exp **target, Exp **length)
{
  Variable *name = edge->GetDirectFunction();

  if (!name)
    return false;

  MemsetFunctionInfo *cur_memset = g_memset_functions;
  while (cur_memset->name) {
    if (TextNameMatch(name, cur_memset->name)) {
      // only handling the case where the value argument passed in is zero.
      if (cur_memset->value_arg < edge->GetArgumentCount()) {
        Exp *value = edge->GetArgument(cur_memset->value_arg);
        if (ExpInt *nvalue = value->IfInt()) {
          long value_int;
          if (nvalue->GetInt(&value_int) && value_int == 0) {
            *target = GetArgumentValue(cur_memset->target_arg);
            *length = GetArgumentValue(cur_memset->length_arg);
            return true;
          }
        }
      }
    }

    cur_memset++;
  }

  const char **cur_zero_allocator = g_zero_allocator_functions;
  while (*cur_zero_allocator) {
    if (TextNameMatch(name, *cur_zero_allocator)) {
      Try(GetAllocationFunction(name, target, length));
      return true;
    }

    cur_zero_allocator++;
  }

  return false;
}

/////////////////////////////////////////////////////////////////////
// Baked Modsets
/////////////////////////////////////////////////////////////////////

// functions which may modify the position of a NULL terminator in one of
// their arguments.
struct TerminateFunctionInfo
{
  // name of the function.
  const char *name;

  // index of the modified argument.
  size_t terminate_arg;

  // whether the argument is definitely terminated by the function.
  bool terminates;
};

static TerminateFunctionInfo g_terminate_functions[] =
{
  // stdlib functions.
  { "strcpy", 0, true },
  { "strcat", 0, true },
  { "strncpy", 0, false },
  { "sprintf", 0, true },
  { "snprintf", 0, true },
  { "vsprintf", 0, true },
  { "vsnprintf", 0, true },

  { NULL, 0, false }
};

void FillBakedModset(BlockModset *mod)
{
  Variable *name = mod->GetId()->BaseVar();

  TerminateFunctionInfo *cur_term = g_terminate_functions;
  while (cur_term->name) {
    if (TextNameMatch(name, cur_term->name)) {
      Exp *arg_exp = GetArgumentValue(cur_term->terminate_arg);
      Exp *kind = GetNullTerminate(NULL);
      mod->AddModset(arg_exp, kind);
    }

    cur_term++;
  }
}

/////////////////////////////////////////////////////////////////////
// Baked Summaries
/////////////////////////////////////////////////////////////////////

// a function whose return value bears a relation with one of its arguments.
struct ReturnCompareFunctionInfo
{
  // name of the function.
  const char *name;

  // binop used for comparison. if this is a pointer binop the pointer
  // type used will be void*/char* (int8).
  BinopKind binop;

  // index of the compared argument.
  size_t compare_arg;
};

static ReturnCompareFunctionInfo g_return_compare_functions[] =
{
  // stdlib functions.
  { "strchr", B_GreaterEqualP, 0 },
  { "strcpy", B_EqualP, 0 },
  { "strcat", B_EqualP, 0 },
  { "memcpy", B_EqualP, 0 },
  { "memset", B_EqualP, 0 },
  { "strncpy", B_EqualP, 0 },
  { "strncat", B_EqualP, 0 },

  { NULL, B_Invalid, 0 }
};

// names of functions which return a NULL terminated C string.
static const char* g_return_terminated_functions[] =
{
  // stdlib functions.
  "strchr",
  "strdup",

  NULL
};

// a strchr function, which searches a string for a particular character.
// these are a subset of the return terminated functions, with the extra
// constraint that if the character is non-zero the terminator position > 0.
struct StrchrFunctionInfo
{
  // name of the function.
  const char *name;

  // index of the string argument to search.
  size_t string_arg;

  // index of the character argument to search for.
  size_t char_arg;
};

static StrchrFunctionInfo g_strchr_functions[] =
{
  // stdlib functions.
  { "strchr", 0, 1 },

  { NULL, 0, 0 }
};

// a strlen function, which returns the zero terminator position of a string.
struct StrlenFunctionInfo
{
  // name of the function.
  const char *name;

  // index of the string argument.
  size_t string_arg;
};

static StrlenFunctionInfo g_strlen_functions[] =
{
  // stdlib functions.
  { "strlen", 0 },

  { NULL, 0 }
};

// a strcmp function, which compares two strings up to their actual length.
struct StrcmpFunctionInfo
{
  // name of the function.
  const char *name;

  // indexes of the two string arguments being compared.
  size_t string_arg_one;
  size_t string_arg_two;
};

static StrcmpFunctionInfo g_strcmp_functions[] =
{
  // stdlib functions.
  { "strcmp", 0, 1 },
  { "strcasecmp", 0, 1 },

  { NULL, 0, 0 }
};

// a strncmp function, which compares two strings up to a specified length.
struct StrncmpFunctionInfo
{
  // name of the function.
  const char *name;

  // indexes of the two string arguments being compared.
  size_t string_arg_one;
  size_t string_arg_two;

  // index of the maximum length to compare to.
  size_t length_arg;
};

static StrncmpFunctionInfo g_strncmp_functions[] =
{
  // stdlib functions.
  { "strncmp", 0, 1, 2 },
  { "strncasecmp", 0, 1, 2 },

  // firefox functions.
  { "PL_strncasecmp", 0, 1, 2 },

  { NULL, 0, 0, 0 }
};

void FillBakedSummary(BlockSummary *sum)
{
  Variable *name = sum->GetId()->BaseVar();

  // primitive memory allocator.

  Exp *object;
  Exp *size;

  if (GetAllocationFunction(name, &object, &size)) {
    Exp *bound = GetByteUpperBound(object);

    // the upper bound is greater or equal to zero.
    Exp *zero = Exp::MakeInt(0);
    Bit *bound_nonneg = Exp::MakeCompareBit(B_GreaterEqual, bound, zero);
    sum->AddAssume(bound_nonneg);

    // the upper bound of the object is exactly equal to size.
    Bit *bound_equal = Exp::MakeCompareBit(B_Equal, bound, size);
    sum->AddAssume(bound_equal);

    // TODO: it would be nice to assert the offset is exactly equal
    // to zero for the UI; however, this can lead to spurious contradiction
    // if unaligned pointers are in use.
  }

  // return value bears some relation with an argument.

  ReturnCompareFunctionInfo *cur_return = g_return_compare_functions;
  while (cur_return->name) {
    if (TextNameMatch(name, cur_return->name)) {
      Exp *ret_exp = GetReturnedValue();
      Exp *arg_exp = GetArgumentValue(cur_return->compare_arg);

      Type *type = NULL;
      if (IsPointerBinop(cur_return->binop))
        type = Type::MakeInt(1, true);

      Bit *bit = Exp::MakeCompareBit(cur_return->binop,
                                     ret_exp, arg_exp, type);
      sum->AddAssume(bit);
    }

    cur_return++;
  }

  // return value is NULL terminated.

  const char **cur_ret_term = g_return_terminated_functions;
  while (*cur_ret_term) {
    if (TextNameMatch(name, *cur_ret_term)) {
      Exp *ret_exp = GetReturnedValue();
      Exp *terminate = GetNullTerminate(ret_exp);
      Exp *zero = Exp::MakeInt(0);

      Bit *bit = Exp::MakeCompareBit(B_GreaterEqual, terminate, zero);
      sum->AddAssume(bit);
    }

    cur_ret_term++;
  }

  // an argument is NULL terminated.

  TerminateFunctionInfo *cur_term = g_terminate_functions;
  while (cur_term->name) {
    if (TextNameMatch(name, cur_term->name) && cur_term->terminates) {
      Exp *arg_exp = GetArgumentValue(cur_term->terminate_arg);
      Exp *kind = GetNullTerminate(NULL);
      Exp *exit_term = Exp::MakeExit(arg_exp, kind);
      Exp *zero = Exp::MakeInt(0);

      Bit *bit = Exp::MakeCompareBit(B_GreaterEqual, exit_term, zero);
      sum->AddAssume(bit);
    }

    cur_term++;
  }

  // strchr constraint: char_arg != 0 => zterm(ret) > 0.

  StrchrFunctionInfo *cur_strchr = g_strchr_functions;
  while (cur_strchr->name) {
    if (TextNameMatch(name, cur_strchr->name)) {
      Exp *arg_exp = GetArgumentValue(cur_strchr->char_arg);
      Exp *ret_exp = GetReturnedValue();
      Exp *terminate = GetNullTerminate(ret_exp);

      Exp *zero = Exp::MakeInt(0);
      Bit *left = Exp::MakeCompareBit(B_NotEqual, arg_exp, zero);
      Bit *right = Exp::MakeCompareBit(B_GreaterThan, terminate, zero);
      Bit *bit = Bit::MakeImply(left, right);
      sum->AddAssume(bit);
    }

    cur_strchr++;
  }

  // strlen constraint: ret >= 0 && ret == zterm(arg)

  StrlenFunctionInfo *cur_strlen = g_strlen_functions;
  while (cur_strlen->name) {
    if (TextNameMatch(name, cur_strlen->name)) {
      Exp *arg_exp = GetArgumentValue(cur_strlen->string_arg);
      Exp *retval = GetReturnedValue();

      Exp *terminate = GetNullTerminate(arg_exp);

      Exp *zero = Exp::MakeInt(0);
      Bit *ge_zero = Exp::MakeCompareBit(B_GreaterEqual, retval, zero);
      sum->AddAssume(ge_zero);

      Bit *eq_term = Exp::MakeCompareBit(B_Equal, retval, terminate);
      sum->AddAssume(eq_term);
    }

    cur_strlen++;
  }

  // strcmp constraint: ret == 0 ==> zterm(arg_one) == zterm(arg_two)

  StrcmpFunctionInfo *cur_strcmp = g_strcmp_functions;
  while (cur_strcmp->name) {
    if (TextNameMatch(name, cur_strcmp->name)) {
      Exp *arg_one_exp = GetArgumentValue(cur_strcmp->string_arg_one);
      Exp *arg_two_exp = GetArgumentValue(cur_strcmp->string_arg_two);
      Exp *retval = GetReturnedValue();

      Exp *terminate_one = GetNullTerminate(arg_one_exp);
      Exp *terminate_two = GetNullTerminate(arg_two_exp);

      Exp *zero = Exp::MakeInt(0);

      Bit *left = Exp::MakeCompareBit(B_Equal, retval, zero);
      Bit *right = Exp::MakeCompareBit(B_Equal, terminate_one, terminate_two);
      Bit *bit = Bit::MakeImply(left, right);
      sum->AddAssume(bit);
    }

    cur_strcmp++;
  }

  // strncmp constraint: ret == 0 ==> (zterm(arg_one) == zterm(arg_two)
  //                                || (zterm(arg_one) >= length_arg &&
  //                                    zterm(arg_two) >= length_arg))

  StrncmpFunctionInfo *cur_strncmp = g_strncmp_functions;
  while (cur_strncmp->name) {
    if (TextNameMatch(name, cur_strncmp->name)) {
      Exp *arg_one_exp = GetArgumentValue(cur_strncmp->string_arg_one);
      Exp *arg_two_exp = GetArgumentValue(cur_strncmp->string_arg_two);
      Exp *length_exp = GetArgumentValue(cur_strncmp->length_arg);
      Exp *retval = GetReturnedValue();

      Exp *terminate_one = GetNullTerminate(arg_one_exp);
      Exp *terminate_two = GetNullTerminate(arg_two_exp);

      Exp *zero = Exp::MakeInt(0);

      Bit *left = Exp::MakeCompareBit(B_Equal, retval, zero);
      Bit *term_eq = Exp::MakeCompareBit(B_Equal, terminate_one, terminate_two);
      Bit *ge_one = Exp::MakeCompareBit(B_GreaterEqual, terminate_one, length_exp);
      Bit *ge_two = Exp::MakeCompareBit(B_GreaterEqual, terminate_two, length_exp);
      Bit *ge_both = Bit::MakeAnd(ge_one, ge_two);
      Bit *right = Bit::MakeOr(term_eq, ge_both);
      Bit *bit = Bit::MakeImply(left, right);
      sum->AddAssume(bit);
    }

    cur_strncmp++;
  }
}

/////////////////////////////////////////////////////////////////////
// GC Safety
/////////////////////////////////////////////////////////////////////

static const char* g_cannotgc_blocks[] = {

  /* Leaves trace and returns first, otherwise PopulateReportBlame could GC. */
  "js_ReportOutOfMemory",

  /* Takes a specialized path when on trace to avoid expanding the stack. */
  "js_InferFlags",

  /*
   * Methods which can throw on error, with the constructed exception possibly
   * triggering a GC. Ignoring these for now, but the real solution is to delay
   * the generation of the exception object until ready to return to script.
   */

  "DeflateStringToUTF8Buffer",
  "DeflateStringToBuffer",
  "InflateUTF8StringToBuffer",
  "InflateStringToBuffer",
  "GetDeflatedUTF8StringLength",

  "allocSlots",
  "reportAllocOverflow",

  "ReportIncompatibleMethod",
  "AdjustBlockSlot",
  "js_ReportOutOfScriptQuota",

  NULL
};

bool BlockCannotGC(BlockId *id)
{
  const char *name = id->BaseVar()->GetSourceName()->Value();

  const char **pos = g_cannotgc_blocks;
  while (*pos) {
    if (!strcmp(*pos, name))
      return true;
    pos++;
  }
  return false;
}

static const char* g_gcthing_types[] = {
  "JSObject",
  "JSString",
  "js::Shape",
  NULL
};

bool TypeIsGCThing(TypeCSU *type)
{
  const char *name = type->GetCSUName()->Value();

  const char **pos = g_gcthing_types;
  while (*pos) {
    if (!strcmp(*pos, name))
      return true;
    pos++;
  }

  return false;
}

Exp* CallConstructsGCRoot(PEdgeCall *edge)
{
  Variable *name = edge->GetDirectFunction();
  if (!name || strcmp(name->GetSourceName()->Value(), "AutoRooter"))
    return NULL;
  if (edge->GetArgumentCount() != 1)
    return NULL;

  Exp *exp = edge->GetArgument(0);
  return exp->IsVar() ? exp : NULL;
}

Exp* CallDestructsGCRoot(PEdgeCall *edge)
{
  Variable *name = edge->GetDirectFunction();
  if (!name || strcmp(name->GetSourceName()->Value(), "~AutoRooter"))
    return NULL;

  Exp *target = edge->GetInstanceObject();
  if (!target || !target->GetType() || !target->GetType()->IsCSU())
    return NULL;

  // inspect the class for a 'ptr' field.
  String *csu_name = target->GetType()->AsCSU()->GetCSUName();
  CompositeCSU *csu = CompositeCSUCache.Lookup(csu_name);

  Exp *res = NULL;
  for (size_t ind = 0; ind < csu->GetFieldCount(); ind++) {
    Field *field = csu->GetField(ind).field;
    if (!strcmp(field->GetSourceName()->Value(), "ptr")) {
      res = Exp::MakeFld(target, field);
      break;
    }
  }

  CompositeCSUCache.Release(csu_name);

  return res;
}

NAMESPACE_XGILL_END
