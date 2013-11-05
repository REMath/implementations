
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

// directions we can propagate from a specific point in the checker search.
// CheckerWhere describes the directions themselves, CheckerPropagate is used
// to determine which CheckerWhere to use for a given point in the search.

NAMESPACE_XGILL_BEGIN

// forward declarations.
class CheckerFrame;

enum WhereKind {
  WK_None,
  WK_Precondition,
  WK_Postcondition,
  WK_Invariant
};

class WhereNone;
class WherePrecondition;
class WherePostcondition;
class WhereInvariant;

// abstract superclass of all checker directions.
class Where
{
 public:
  // priority-based comparison function, return negative if where0 is 'better'
  // than where1, positive if where1 is better than where0, zero if the two
  // are not comparable. we like directions that are most likely to lead to
  // a shorter proof of the eventual assert.
  static int PriorityCompare(Where *where0, Where *where1);

  // make the safe bits for an initial assertion on cond.
  static void GetAssertBits(CheckerFrame *frame, PPoint point,
                            Bit *assert_cond, GuardBitVector *res);

 public:
  Where(WhereKind kind, Bit *bit)
    : m_kind(kind), m_bit(bit)
  {}

  WhereKind Kind() const { return m_kind; }
  Bit* GetBit() const { return m_bit; }

  DOWNCAST_TYPE(Where, WK_, None)
  DOWNCAST_TYPE(Where, WK_, Precondition)
  DOWNCAST_TYPE(Where, WK_, Postcondition)
  DOWNCAST_TYPE(Where, WK_, Invariant)

  virtual void Print(OutStream &out) const = 0;
  virtual void PrintUI(OutStream &out) const = 0;

  // print the name of the hook function to use when adding an annotation
  // for this kind of direction. if there are multiple functions then
  // they will be separated by a '$'.
  virtual void PrintHook(OutStream &out) const { Assert(false); }

 private:
  WhereKind m_kind;

 protected:
  Bit *m_bit;
};

// print Where values directly to a stream.
inline OutStream& operator << (OutStream &out, const Where *w)
{
  Assert(w);
  w->Print(out);
  return out;
}

// ways in which the checker exploration can be terminated.
enum ReportKind
{
  // check was not a report. reserved for zero so we can test for proper
  // report values with != 0.
  RK_None = 0,

  // exhausted exploration along a particular path and the error is still
  // satisfiable.
  RK_Finished,

  // the exploration soft timeout was reached.
  RK_Timeout,

  // failed to find a loop sufficient condition or otherwise block recursion.
  RK_Recursion,

  // unknown expression in safe bit during backwards propagation.
  RK_Unexpected,

  // could not identify base object for type invariant.
  RK_UnknownCSU,

  // depends on a postcondition for a callee with no implementation.
  RK_NoCallee
};

inline const char* ReportString(ReportKind kind)
{
  switch (kind) {
  case RK_None:        return "None";
  case RK_Finished:    return "Finished";
  case RK_Timeout:     return "Timeout";
  case RK_Recursion:   return "Recursion";
  case RK_Unexpected:  return "Unexpected";
  case RK_UnknownCSU:  return "UnknownCSU";
  case RK_NoCallee:    return "NoCallee";
  }

  Assert(false);
  return NULL;
}

// Where instance classes

class WhereNone : public Where
{
 public:
  WhereNone(ReportKind report_kind);

  ReportKind GetReportKind() const { return m_report_kind; }
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;

 private:
  // kind of the failed propagation. use None to block propagation without
  // generating a report.
  ReportKind m_report_kind;
};

class WherePrecondition : public Where
{
 public:
  // try to make a WherePrecondition from id/bit, NULL otherwise.
  static Where* Make(BlockMemory *mcfg, Bit *bit);

 public:
  WherePrecondition(BlockMemory *mcfg, Bit *bit);

  BlockMemory* GetMemory() const { return m_mcfg; }
  bool IsIgnoreUnroll() const { return m_ignore_unroll; }
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;
  void PrintHook(OutStream &out) const;

  // make the caller safe bits when the frame for this precondition is invoked
  // by the specified caller frame and call point.
  void GetCallerBits(CheckerFrame *caller_frame, PPoint point,
                     Bit **base_bit, GuardBitVector *res);

 private:
  // mcfg this is a precondition for. may be for a function or loop iteration.
  // the bit holds at entry to this frame.
  BlockMemory *m_mcfg;

  // for preconditions on loops (aka loop invariants), ignore loop unrolls
  // equalities with callers, letting us capture all possible behaviors
  // of the loop.
  bool m_ignore_unroll;
};

class WherePostcondition : public Where
{
 public:
  // try to make a WherePostcondition from frame/point/bit, NULL otherwise.
  static Where* Make(CheckerFrame *frame, PPoint point, Bit *bit);

 public:
  WherePostcondition(CheckerFrame *frame, PPoint point, Bit *bit);

  CheckerFrame* GetFrame() const { return m_frame; }
  PPoint GetPoint() const { return m_point; }
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;
  void PrintHook(OutStream &out) const;

  // make the safe bits when the frame for this postcondition invokes a loop
  // which executes for zero iterations.
  void GetSkipLoopBits(Bit **base_bit, GuardBitVector *res);

  // make the callee safe bits when the frame for this postcondition invokes
  // the specified callee frame.
  void GetCalleeBits(CheckerFrame *callee_frame,
                     Bit **base_bit, GuardBitVector *res);

 private:
  // checker frame whose callees we are checking postconditions on.
  CheckerFrame *m_frame;

  // point in the checker frame whose callees we are checking. the callees
  // may be a function call (direct or indirect) or a loop.
  // the bit holds at exit from the possible callees.
  PPoint m_point;
};

class WhereInvariant : public Where
{
 public:
  // try to make an invariant from bit based on lval, which is of type csu.
  // if csu/lval are NULL then try to make a global invariant.
  static Where* Make(TypeCSU *csu, Exp *lval, Bit *bit);

 public:
  WhereInvariant(TypeCSU *csu, Variable *var, Bit *bit);

  TypeCSU* GetCSU() const { return m_csu; }
  void Print(OutStream &out) const;
  void PrintUI(OutStream &out) const;
  void PrintHook(OutStream &out) const;

  // make the safe bits within a write frame when writes are performed using
  // the specified write_csu. write_csu is NULL for global invariants,
  // or the lval of the CSU for type invariants. base_csu indicates the
  // point-relative CSU being written.
  void GetHeapBits(CheckerFrame *write_frame,
                   Exp *write_csu, Exp *base_csu,
                   Bit **base_bit, GuardBitVector *res);

  // assert any conditions implied by this invariant which are relevant
  // to a read from exp within frame.
  void AssertRecursive(CheckerFrame *frame, Exp *exp);

  // for type invariants, if lval is written to in some frame then return the
  // expression for the base CSU itself, NULL if the base cannot be determined.
  Exp* GetWriteCSU(Exp *lval);

 private:
  // type being quantified over. NULL for purely global invariants.
  // if NULL, the bit refers only to global variables. otherwise, the bit
  // may contain 'this' to refer to the value of type m_csu.
  TypeCSU *m_csu;

  // optional global variable to hang a global invariant on. for printing
  // hooks so that we know where to attach the inserted annotation.
  Variable *m_var;
};

// remove any uses of ExpVal or ExpFrame (for the specified frame) from the
// list of input exps/bits, storing the result in output.
void RemoveValExp(FrameId frame, BlockMemory *mcfg,
                  const GuardExpVector &input, GuardExpVector *output);
void RemoveValBit(FrameId frame, BlockMemory *mcfg,
                  const GuardBitVector &input, GuardBitVector *output);

NAMESPACE_XGILL_END
