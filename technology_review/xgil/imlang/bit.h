
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

#include "exp.h"

NAMESPACE_XGILL_BEGIN

enum BitKind {
  BIT_Invalid = 0,
  BIT_False = 1,
  BIT_True = 2,
  BIT_Var = 3,
  BIT_Not = 4,
  BIT_And = 5,
  BIT_Or = 6
};

// size of built-in storage for bit formulas. if the number of operands
// for the bit is <= this it does not need additional dynamic allocation.
#define BIT_BASE_CAPACITY 4

// depth to recurse into sub-operands when replacing implied bits.
// 0 is no recursion, just remove duplicates/contradictions from
// the top-level binop.
#define REPLACE_IMPLIED_DEPTH 4

// maximum possible replace implied depth.
#define REPLACE_IMPLIED_MAX_DEPTH ((uint32_t)-1)

enum BitSimplifyLevel {
  BSIMP_None = 0, // don't do any simplification
  BSIMP_Fold = 1, // constant fold and other trivial simplification
  BSIMP_Full = 2  // full simplification
};

// the type of boolean formulas over expressions
class Bit : public HashObject
{
 public:
  static int Compare(const Bit *b0, const Bit *b1);
  static Bit* Copy(const Bit *b);

  static void Write(Buffer *buf, Bit *b);
  static Bit* Read(Buffer *buf);

  // each of these Make() functions adds a reference to their
  // result Bit, in the same way as HashCons.Lookup().
  // they also consume a reference for each operand Bit or T passed in

  // get a constant true/false bit.
  static Bit* MakeConstant(bool constant);

  // get a bit which is true iff var != 0.
  static Bit* MakeVar(Exp *var);

  // get the negation of a bit.
  static Bit* MakeNot(Bit *op,
                      BitSimplifyLevel level = BSIMP_Full);

  // get the conjunction of two bits, or of a list of bits.
  static Bit* MakeAnd(Bit *op0, Bit *op1,
                      BitSimplifyLevel level = BSIMP_Full);
  static Bit* MakeAnd(const Vector<Bit*> &op_list,
                      BitSimplifyLevel level = BSIMP_Full);

  // get the disjunction of two bits, or of a list of bits.
  static Bit* MakeOr(Bit *op0, Bit *op1,
                     BitSimplifyLevel level = BSIMP_Full);
  static Bit* MakeOr(const Vector<Bit*> &op_list,
                     BitSimplifyLevel level = BSIMP_Full);

  // get the implication 'op0 => op1'
  static Bit* MakeImply(Bit *op0, Bit *op1,
                        BitSimplifyLevel level = BSIMP_Full);

  // reduce bit by converting to true/false any sub-formulas implied by
  // a base condition. the (result & base) is equivalent to (bit & base).
  // consumes a reference on bit but *not* on base, and gets a reference
  // on the result.
  static Bit* ReduceBit(Bit *bit, Bit *base);

 public:
  // get the kind of this bit.
  BitKind Kind() const { return m_kind; }

  // is this a constant true or false bit?
  bool IsTrue() const { return m_kind == BIT_True; }
  bool IsFalse() const { return m_kind == BIT_False; }

  // returns the variable this bit represents for BIT_Var,
  // NULL otherwise.
  Exp* GetVar() const { return m_var; }

  // get the operands of this bit for BIT_Not, BIT_And or BIT_Or.
  // Number of operands is zero for other kinds.
  size_t GetOperandCount() const { return m_op_count; }

  // get a particular operand of this bit
  Bit* GetOperand(size_t op) const {
    Assert(op < GetOperandCount());
    return m_ops ? m_ops[op] : m_base_ops[op];
  }

  // get the number of nodes in this bit. if the same and/or/not is used
  // multiple times it will only be counted once.
  size_t Size();

  // print this bit for the UI.
  void PrintUI(OutStream &out, bool parens) const;

  // print out this bit in a formatted tree representation,
  // with the specified amount of padding before each line.
  void PrintTree(OutStream &out, size_t pad_spaces);

  // visit the expressions in this bit with the specified visitor/mapper.
  // if revisit is set then child bits will only be visited the first
  // time they are encountered (revisit == true allows reentrancy).
  void DoVisit(ExpVisitor *visitor, bool revisit = false);
  Bit* DoMap(ExpMapper *mapper);
  void DoMultiMap(ExpMultiMapper *mapper, Vector<Bit*> *res);

  // inherited methods
  void Print(OutStream &out) const;
  void MarkChildren() const;
  void Persist();
  void UnPersist();

 private:
  BitKind m_kind;

  // data for BIT_Var.
  Exp *m_var;

  // data for BIT_And/BIT_Or/BIT_Not. m_ops is non-NULL iff
  // m_op_count > BIT_BASE_CAPACITY, in which case a heap buffer is
  // created for the bits.
  size_t m_op_count;
  Bit* m_base_ops[BIT_BASE_CAPACITY];
  Bit* *m_ops;

  // helpers for recursive methods.
  size_t RecursiveSize();
  void RecursivePrintTree(OutStream &out, size_t pad_spaces);
  void RecursiveVisit(ExpVisitor *visitor, bool revisit);

 private:
  static Bit* SimplifyBit(Bit &bit,
                                BitSimplifyLevel level);

  static void SimplifyConstantFold(Bit **pbit);
  static void SimplifyDegenerate(Bit **pbit);
  static void SimplifyDeMorgan(Bit **pbit);
  static void SimplifyFlatten(Bit **pbit);
  static void SimplifyRefactor(Bit **pbit);
  static void SimplifyImplied(Bit **pbit);

  // helpers for SimplifyImplied
  static Bit* ReplaceImplied(Bit *bit, const Vector<Bit*> &operands,
                             size_t cur_operand, bool operands_true,
                             size_t depth);
  static bool IsBitImplied(Bit *bit, Bit *xbit,
                           bool xbit_true, bool *bit_true);

 public:

  // scratch field for use by analyses which crawl Bits. since Bits
  // are in general DAGs rather than trees, a plain recursive crawl
  // may end up taking time exponential in the DAG size. instead,
  // crawls should store data on traversed bits here and use that
  // instead of revisiting a bit. after the crawl, the tree must be
  // crawled a second time to clear out this field in all previously
  // traversed bits.
  void *m_extra;

  // clear out all extra information in this bit and its transitive operands.
  void ClearExtra();

  // whether m_extra is in use for any bits. use to prevent reentrance.
  static bool g_extra_used;

 private:

  // scratch field reserved for Bit::ReplaceImplied.
  Bit *m_replace_extra;

  // scratch field reserved for Size, DoVisit and PrintTree.
  bool m_base_extra;

  // clear replace/extra information on this bit.
  void ClearReplaceExtra();
  void ClearBaseExtra();

  // whether m_replace_extra/m_base_extra are in use for any bits.
  // use to prevent reentrance.
  static bool g_replace_used;
  static bool g_base_used;

  Bit(bool constant);
  Bit(Exp *var);
  Bit(BitKind kind, const Vector<Bit*> &data);
  static HashCons<Bit> g_table;
};

// sorting and duplicate removal for bit objects
inline void SortBitList(Vector<Bit*> *pdata)
{
  SortObjectsRmDups<Bit>(pdata);
}

// are the bits in data sorted per SortBitList?
inline bool IsSortedBitList(const Vector<Bit*> &data)
{
  return IsSortedObjectsRmDups<Bit>(data);
}

// serialization

// cached bit tag. first child must be a TAG_UInt32, which is an ID
// for a bit either previously seen or for the one being serialized.
// if the former, this is the only child. if the latter, contains
// the following remaining children:
//   TAG_Kind (all)
//   TAG_Exp (var)
//   ordered list of TAG_Bit (and, not, or)
#define TAG_Bit  1080

// miscellaneous

bool BitHasDirective(Bit *bit, DirectiveKind kind);
bool BitHasAnyDirective(Bit *bit);

NAMESPACE_XGILL_END
