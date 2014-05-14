
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

// visitor classes for language structures.

NAMESPACE_XGILL_BEGIN

// forward declarations.
class Exp;

// kinds of visits to do over an analysis structure (an exp, bit or CFG edge).
// this specifies which expressions the visitor will be invoked on, depending
// on where in the structure the expression appears.
enum ExpVisitorKind
{
  // visit all expressions within the structure.
  VISK_All,

  // visit only lvalue expressions whose value is read or written while
  // executing the structure. during mapping this behaves as VISK_All.
  VISK_Lval,

  // visit the Lval expressions and their subexpressions. during mapping
  // this behaves as VISK_All.
  VISK_LvalSubExprs,

  // visit the subexpressions of an initial lvalue expression.
  VISK_SubExprs,

  // visit the leaf terms in a bit or rvalue expression, but do not dig
  // into the subexpressions of those leaves.
  VISK_Leaf,

  // visit the leaf variables in a bit.
  VISK_BitLeaf
};

// recurse on lvalue subexpressions for the specified visitor kind.
inline bool TryLvalRecurse(ExpVisitorKind kind) {
  switch (kind) {
  case VISK_Leaf:
  case VISK_BitLeaf:
    return false;
  default:
    return true;
  }
}

// recurse on rvalue subexpressions.
inline bool TryRvalRecurse(ExpVisitorKind kind) {
  switch (kind) {
  case VISK_SubExprs:
  case VISK_BitLeaf:
    return false;
  default:
    return true;
  }
}

// interface structure for crawling the expressions in a structure.
class ExpVisitor
{
 public:
  ExpVisitor(ExpVisitorKind kind)
    : m_kind(kind), m_found_lval(false), m_found_term(false),
      m_negative_phase(false), m_ignore_disjunction(false),
      m_finished(false)
  {}

  // get the kind of this visitor.
  ExpVisitorKind Kind() const { return m_kind; }

  // set/get whether this is contained in an lval.
  bool FoundLval() const { return m_found_lval; }
  bool SetFoundLval(bool found_lval) {
    bool old_found_lval = m_found_lval;
    m_found_lval = found_lval;
    return old_found_lval;
  }

  // get whether this is contained in an expression term or not.
  bool FoundTerm() const { return m_found_term; }
  bool SetFoundTerm(bool found_term) {
    bool old_found_term = m_found_term;
    m_found_term = found_term;
    return old_found_term;
  }

  // get whether this value occurs in negative vs. positive phase
  // if it is contained within a Bit.
  bool NegativePhase() { return m_negative_phase; }

  // flip the phase of this visitor.
  void FlipPhase() { m_negative_phase = !m_negative_phase; }

  // whether to ignore during the visit expressions in a Bit disjunction.
  bool IgnoreDisjunction() { return m_ignore_disjunction; }

  // queries for use in visitor recursion.

  // whether this visitor is finished and no further recursion
  // on subexpressions should be performed.
  bool IsFinished() const { return m_finished; }

  // visit each expression found during DoVisit traversal.
  bool IsVisiting() const {
    switch (m_kind) {
    case VISK_Lval:
      return false;
    case VISK_LvalSubExprs:
      return FoundLval();
    default:
      return true;
    }
  }

  // whether to recurse according to the kind of this visitor.
  bool LvalRecurse() { return TryLvalRecurse(m_kind); }
  bool RvalRecurse() { return TryRvalRecurse(m_kind); }

  // operation to perform when invoked on an expression.
  virtual void Visit(Exp *value) = 0;

 protected:
  ExpVisitorKind m_kind;
  bool m_found_lval;
  bool m_found_term;
  bool m_negative_phase;
  bool m_ignore_disjunction;
  bool m_finished;
};

// kinds of ways to handle mapping bits when only a portion of that bit
// is has a target in the mapping.
enum ExpWidenKind
{
  // drop the entire outer bit containing the non-mapped expressions.
  WIDK_Drop,

  // convert the bit to one which it implies, A => TRUE
  WIDK_Widen,

  // convert the bit to one which implies it, A => FALSE
  WIDK_Narrow
};

// interface structure for mapping the expressions in a structure.
class ExpMapper
{
 public:
  ExpMapper(ExpVisitorKind kind, ExpWidenKind widen)
    : m_kind(kind), m_widen(widen)
  {}

  // get the kind of this mapper.
  ExpVisitorKind Kind() { return m_kind; }

  // get the way in which NULL operands in a bit should be handled.
  ExpWidenKind Widen() { return m_widen; }

  // flip the widening information in this mapper.
  void FlipWiden() {
    switch (m_widen) {
    case WIDK_Drop:    break;
    case WIDK_Widen:   m_widen = WIDK_Narrow; break;
    case WIDK_Narrow:  m_widen = WIDK_Widen;  break;
    }
  }

  // whether to recurse according to the kind of this mapper.
  bool LvalRecurse() { return TryLvalRecurse(m_kind); }
  bool RvalRecurse() { return TryRvalRecurse(m_kind); }

  // get the result of mapping an exp either to NULL or to another exp.
  // value indicates the exp after its children were mapped, old indicates
  // the exp beforehand. if mapping any children of the exp returned NULL
  // then value itself will be NULL (old is never NULL). consumes a reference
  // on value if non-NULL, gets a reference on the result if non-NULL.
  virtual Exp* Map(Exp *value, Exp *old) = 0;

 private:
  ExpVisitorKind m_kind;
  ExpWidenKind m_widen;
};

// interface structure for mapping expressions to possibly multiple exps.
class ExpMultiMapper
{
 public:
  ExpMultiMapper(ExpVisitorKind kind, size_t limit = 0)
    : m_kind(kind), m_limit(limit)
  {}

  // get the kind of this mapper.
  ExpVisitorKind Kind() { return m_kind; }

  // whether to recurse according to the kind of this mapper.
  bool LvalRecurse() { return TryLvalRecurse(m_kind); }
  bool RvalRecurse() { return TryRvalRecurse(m_kind); }

  // returns the maximum tolerated result size, 0 for no limit.
  size_t ResultLimit() { return m_limit; }

  // get the result of multi-mapping value to zero or more other expressions.
  // value will be non-NULL. consumes a reference on exp.
  virtual void MultiMap(Exp *exp, Vector<Exp*> *res) = 0;

 protected:
  ExpVisitorKind m_kind;

  // for controlling potential explosion in result size.
  size_t m_limit;
};

NAMESPACE_XGILL_END
