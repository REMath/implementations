
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

// summary information inferred for each block. the code which actually
// fills in this structure is in the infer directory.

#include "mblock.h"

NAMESPACE_XGILL_BEGIN

// kinds of program assertions.
enum AssertKind {
  ASK_None = 0,

  // conditions from a checked annotation.
  ASK_Annotation = 1,
  ASK_AnnotationRuntime = 2,

  // annotation conditions to defer until the end of the block.
  ASK_Invariant = 3,

  // checking for a buffer write overflow/underflow.
  ASK_WriteOverflow = 10,
  ASK_WriteUnderflow = 11,

  // checking for a buffer read overflow/underflow.
  ASK_ReadOverflow = 12,
  ASK_ReadUnderflow = 13,

  // checking for an overflow/underflow in an integer operation.
  ASK_IntegerOverflow = 14,
  ASK_IntegerUnderflow = 15,

  // GC-safe memory accesses.
  ASK_GCSafe = 20,
  ASK_CanGC = 21
};

// classes of program assertions.
enum AssertClass {
  // assertions that trivially hold; they are either tautological or are
  // implied by the guard at the point they are asserted.
  ASC_Trivial = 0,

  // assertions that are implied by one or more other assertions.
  // if all the ASC_Check assertions for a given kind are proved,
  // the redundant ones are also proved.
  ASC_Redundant = 1,

  // assertions which need to be checked to determine whether they hold.
  ASC_Check = 2
};

inline const char* AssertKindString(AssertKind kind)
{
  switch (kind) {
  case ASK_None:               return "none";

  case ASK_Annotation:         return "annotation";
  case ASK_AnnotationRuntime:  return "annotation_runtime";
  case ASK_Invariant:          return "invariant";

  case ASK_WriteOverflow:      return "write_overflow";
  case ASK_WriteUnderflow:     return "write_underflow";
  case ASK_ReadOverflow:       return "read_overflow";
  case ASK_ReadUnderflow:      return "read_underflow";
  case ASK_IntegerOverflow:    return "integer_overflow";
  case ASK_IntegerUnderflow:   return "integer_underflow";

  case ASK_GCSafe:             return "gcsafe";
  case ASK_CanGC:              return "cangc";

  default: Assert(false);
  }
}

inline const char* AssertClassString(AssertClass cls)
{
  switch (cls) {
  case ASC_Trivial:    return "trivial";
  case ASC_Redundant:  return "redundant";
  case ASC_Check:      return "check";
  default: Assert(false);
  }
}

// information about a program assertion.
struct AssertInfo
{
  // kind and class of assertion.
  AssertKind kind;
  AssertClass cls;

  // point the assertion occurs at.
  PPoint point;

  // bit being asserted. this bit is expressed in terms of the state at point.
  Bit *bit;

  // globally unique name of this assertion, if computed. names have the
  // format 'kind$filename$function$loop$index'. this format allows us
  // to process and filter assertions easily using scripts.
  Buffer *name_buf;

  AssertInfo()
    : kind(ASK_None), cls(ASC_Trivial), point(0), bit(NULL), name_buf(NULL) {}
};

// information about a program assumption. these are not stored in the summary
// itself but are generated on demand.
struct AssumeInfo
{
  // annotation this assumption came from, if there is one.
  BlockCFG *annot;

  // point where this assumption came from, if there is one.
  PPoint point;

  // bit being assumed. unlike AssertInfo, this is expressed in terms of the
  // state at CFG entry.
  Bit *bit;

  AssumeInfo() : annot(NULL), point(0), bit(NULL) {}
};

// remove duplicates in a list of assumptions.
inline void CombineAssumeList(Vector<AssumeInfo> *assumes)
{
  for (size_t ind = 0; ind < assumes->Size(); ind++) {
    bool duplicate = false;
    const AssumeInfo &info = assumes->At(ind);
    for (size_t xind = 0; xind < ind; xind++) {
      if (info.bit == assumes->At(xind).bit)
        duplicate = true;
    }
    if (duplicate) {
      assumes->At(ind) = assumes->Back();
      assumes->PopBack();
      ind--;
    }
  }
}

class BlockSummary : public HashObject
{
 public:
  static int Compare(const BlockSummary *sum0, const BlockSummary *sum1);
  static BlockSummary* Copy(const BlockSummary *sum);
  static void Write(Buffer *buf, const BlockSummary *sum);
  static BlockSummary* Read(Buffer *buf);

  static void WriteList(Buffer *buf, const Vector<BlockSummary*> &sum_list);
  static void ReadList(Buffer *buf, Vector<BlockSummary*> *sum_list);

  static BlockSummary* Make(BlockId *id) {
    BlockSummary xsum(id);
    return g_table.Lookup(xsum);
  }

  // adds all bits to assume for mcfg to assumed_list. these bits can come
  // from the summary or annotations on mcfg and its callees. only assertions
  // earlier than end_point are included.
  static void GetAssumedBits(BlockMemory *mcfg, PPoint end_point,
                             Vector<AssumeInfo> *assume_list);

  // parse the name of a function which contains the specified assertion name.
  // appends that name to buf, including the NULL terminator. returns whether
  // the parse was successful.
  static bool GetAssertFunction(const char *name, Buffer *buf);

  // whether a field is traversed on GC and always safe to access.
  static bool FieldIsGCSafe(Field *field);

 public:
  // get the ID of the CFG for this block.
  BlockId* GetId() const { return m_id; }

  // set the memory for this block. mcfg->GetId() == GetId().
  // holds a reference on mcfg which persists until the summary goes away.
  void SetMemory(BlockMemory *mcfg);

  // get the block this is generating a summary for, if available.
  BlockMemory* GetMemory() const { return m_mcfg; }

  // assertions made at the points in this block.
  const Vector<AssertInfo>* GetAsserts() const { return m_assert_list; }
  void AddAssert(AssertKind kind, AssertClass cls, PPoint point, Bit *bit);

  // inferred assumptions which can be instantiated in the callers.
  // these do not refer to any internal state.
  const Vector<Bit*>* GetAssumes() const { return m_assume_list; }
  void AddAssume(Bit *bit);

  // fill in the names of all assertions in this summary.
  void ComputeAssertNames();

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  // General summary information.

  BlockId *m_id;

  // memory we are generating a summary for, if available.
  BlockMemory *m_mcfg;

  Vector<AssertInfo> *m_assert_list;
  Vector<Bit*> *m_assume_list;

 private:
  // create empty summary information for the specified block.
  BlockSummary(BlockId *id);

  static HashCons<BlockSummary> g_table;
};

NAMESPACE_XGILL_END
