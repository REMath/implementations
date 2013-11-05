
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

// interface to backend solver for answering queries about Bit formulas.
// the functionality we need from a solver is as follows:
// - able to handle arithmetic and uninterpreted functions,
//   without quantifiers.
// - incremental solving capability.
// - able to generate satisfying assignments.

// only one backend solver can be in use by a process. this interface is
// designed to easily switch between backends at compile time and compare
// their performance.

#include <memory/mblock.h>
#include <util/config.h>
#include "solver_hash.h"
#include "constraint.h"

NAMESPACE_XGILL_BEGIN

extern ConfigOption solver_use;
extern ConfigOption solver_verbose;
extern ConfigOption solver_constraint;

// expressions returned as the result of translation to the underlying
// solver's representation. SlvExpr values can represent either a boolean
// or integral value; the two may have different representations for the
// underlying solver. NULL is not a legal value for a SlvExpr value.
typedef void* SlvExpr;

// values representing an unconstrained variable declaration in the underlying
// solver. an SlvExpr expression can be fetched for a given SlvDecl, and the
// value of a declaration can be queried for a solver's satisfying assignment.
typedef void* SlvDecl;

// pair of an expression and the solver frame in which it occurs.
struct FrameExp {
  FrameId frame;
  Exp *exp;

  FrameExp() : frame(0), exp(NULL) {}
  FrameExp(int) : frame(0), exp(NULL) {}  // needed as SolverHash data.
  FrameExp(FrameId _frame, Exp *_exp) : frame(_frame), exp(_exp) {}

  static uint32_t Hash(uint32_t hash, FrameExp info) {
    hash = Hash32(hash, info.frame);
    return Hash32(hash, info.exp->Hash());
  }

  bool operator == (const FrameExp &o) const {
    return (frame == o.frame) && (exp == o.exp);
  }
};

// structure wrapping the mpz_t type. mpz_t is an array (for implicit
// address-of when calling functions) and doesn't work well when used
// in a vector or hash table.
struct mpz_value {
  mpz_t n;
};

// forward declaration.
class Solver;

// type of a solver assignment, mapping Frame/Exp pairs to the value
// assigned to them.
typedef HashTable<FrameExp,mpz_value,FrameExp> SolverAssignment;

typedef SolverHashTable<Exp,SlvDecl> SolverDeclTable;
typedef SolverHashTable<Exp,SlvExpr> SolverExpTable;
typedef SolverHashTable<Bit,SlvExpr> SolverBitTable;

// interface used to interact with a backend external solver. this is the bare
// minimum level of functionality we need from a backend. all interaction
// we do with this interface is through the Solver class below.
class BaseSolver
{
 public:
  BaseSolver(Solver *parent) : m_parent(parent) {}

  // a BaseSolver will be destroyed only after calling Clear on it.
  virtual ~BaseSolver() {}

  // get the name of this backend.
  virtual const char* Name() const = 0;

  // print any detailed timer information for this backend. aggregate timing
  // information will be taken care of by Solver::PrintTimers.
  virtual void PrintTimers() const {}

  // methods analogous to those in Solver.
  virtual void Clear() = 0;
  virtual void PushContext() = 0;
  virtual void PopContext() = 0;

  // make an integral constant.
  virtual SlvExpr MakeIntegralConstantMpz(const mpz_t value) = 0;
  virtual SlvExpr MakeIntegralConstant(long value) = 0;

  // make a boolean constant.
  virtual SlvExpr MakeBooleanConstant(bool value) = 0;

  // make a declaration for an unconstrained variable unique to the specified
  // frame/exp. will not be called multiple times for the same frame/exp.
  // use Solver::IsBoolean and Solver::IsNonNegative to determine whether
  // the declaration is boolean or nonnegative.
  virtual SlvDecl MakeDeclaration(FrameId frame, Exp *exp) = 0;

  // get an expression for the value of an unconstrained variable declaration.
  virtual SlvExpr GetDeclarationExpr(SlvDecl decl) = 0;

  // gets the result of applying a unary operation to a particular value.
  // op_boolean and res_boolean indicate whether the operand and unop result
  // are boolean. for LNot both are boolean, otherwise both are integral.
  virtual SlvExpr GetUnop(UnopKind unop, SlvExpr exp) = 0;

  // gets the result of applying a binary operation to particular values.
  // left_boolean, right_boolean, and res_boolean indicate whether the
  // operands and binop result are boolean. for LAnd and LOr all will be
  // boolean, for comparisons the operands are integral and result boolean,
  // otherwise all are integral.
  virtual SlvExpr GetBinop(BinopKind binop,
                           SlvExpr left_exp, SlvExpr right_exp) = 0;

  // gets an expression for an uninterpreted function application
  // for the specified unop or binop.
  virtual SlvExpr GetUninterpretedUnop(UnopKind unop, SlvExpr exp) = 0;
  virtual SlvExpr GetUninterpretedBinop(BinopKind binop,
                                        SlvExpr left_exp,
                                        SlvExpr right_exp) = 0;

  // coerce an integral value to a boolean value. ne_zero indicates whether
  // the result should be for (value != 0) or (value == 0)
  virtual SlvExpr CoerceIntToBool(SlvExpr exp, bool ne_zero) = 0;

  // coerce a boolean value to an integral value. the result should be one
  // if (value != 0), or 0 if (value == 0).
  virtual SlvExpr CoerceBoolToInt(SlvExpr exp) = 0;

  // assert the specified expression within the solver. exp is a boolean.
  virtual void BaseAssert(SlvExpr exp) = 0;

  // return whether the asserted expressions are satisfiable.
  virtual bool BaseCheck() = 0;

  // fills in assign with data from the current satisfying assignment.
  // decl_table indicates the declarations for every uninterpreted variable,
  // as returned by MakeDeclaration.
  virtual void GetAssignment(SolverDeclTable &decl_table,
                             SolverAssignment &assign) = 0;

  // analogous to Solver method.
  virtual void PrintUnsatCore() = 0;

  // print the raw solver representation of exp to cout (not the log).
  virtual void PrintRawData(SlvExpr exp, bool is_boolean) = 0;

  // debugging methods. print input to pass to the backend independently.

  virtual void DebugPrintDecl(SlvDecl decl, bool is_boolean) {}
  virtual void DebugPrintAssign(SlvDecl decl, const mpz_t value) {}
  virtual void DebugPrintAssert(SlvExpr expr) {}

 protected:
  Solver *m_parent;
};

// solver providing additional functionality over a BaseSolver to answer
// queries and generate satisfying assignments for Bits and Exps.
class Solver
{
  // make the base solver implementations friends so they can see the private
  // data in this class. this is mostly for debugging.
  friend class SolverYices;
  friend class SolverCVC3;
  friend class SolverMUX;

 public:
  // utility functions for checking properties of exps and bits independent
  // of any existing solvers.

  // whether a particular bit is satisfiable or valid, irrespective of any
  // context in which it appears.
  static bool BitSatisfiable(Bit *bit);
  static bool BitValid(Bit *bit);

  // whether two bits imply one another or are equivalent.
  static bool BitImplies(Bit *bit0, Bit *bit1);
  static bool BitEquivalent(Bit *bit0, Bit *bit1);

  // check that the bits in bit_list are pairwise disjoint modulo guard
  // and join to guard
  static void CheckDisjointBits(Bit *guard,
                                const Vector<Bit*> &bit_list);

  // check equivalence between various exps and bits, print an error if they
  // are not semantically equivalent according to the underlying solver.
  static void CheckEquivalentExp(Exp *exp0, Exp *exp1);
  static void CheckEquivalentCvt(Exp *exp0, Bit *bit1);
  static void CheckEquivalentBit(Bit *bit0, Bit *bit1);

  // calling this function enables equivalence checking on all simplifications
  // performed when constructing exp and bit values. this is very
  // expensive and should just be used for occasional debugging.
  static void CheckSimplifications();

  // is the result of ConvertExp(exp) a boolean or an integral value?
  static bool IsBoolean(Exp *exp);

  // for declaration expressions, must the value of exp be nonnegative?
  static bool IsNonNegative(Exp *exp);

  // for a declaration, 

 public:
  Solver(const char *name);
  ~Solver() { Clear(); delete m_base; }

  // the number of contexts that have been pushed onto this solver.
  size_t GetContextCount() { return m_context_count; }

  // whether the behavior of this solver will be printed to the screen.
  bool Verbose() { return m_verbose; }
  void SetVerbose(bool verbose) { m_verbose = verbose; }

  // get a new frame for asserting conditions about the specified memory
  // (which may be NULL). frame zero will not be returned here.
  FrameId MakeFrame(BlockMemory  *mcfg) {
    m_frames.PushBack(mcfg);
    return m_frames.Size() - 1;
  }

  // print timing information for this solver to the log.
  void PrintTimers();

  // add an assertion to the context of this solver.
  void AddAssert(FrameId frame, Bit *bit, bool side_conditions = false);

  // add side conditions and pending information for the specified bit,
  // but do not actually assert it.
  void AddSideConditions(FrameId frame, Bit *bit);

  // add conditional assertions for every bit in a guarded list.
  void AddAssertList(FrameId frame, const GuardBitVector &bit_list,
                     bool side_conditions = false);

  // add an assertion without updating the pending terms.
  // unlike AddAssert, this consumes a reference on bit.
  void AddConstraint(FrameId frame, Bit *bit);

  // expand an uninterpreted Val or offset of a Val in this frame.
  // returns true if the expression was a Val that could be expanded.
  bool ExpandVal(FrameId frame, Exp *exp,
                 bool pending = true);

  // add a conditional equality between terms in two frames. exp_one in
  // frame_one equals exp_two in frame_two if cond_one holds in frame_one
  // and cond_two holds in frame_two.
  void AddEquality(FrameId frame_one, FrameId frame_two,
                   Exp *exp_one, Bit *cond_one, bool pending_one,
                   Exp *exp_two, Bit *cond_two, bool pending_two);

  // get all uninterpreted terms (any lvalue/val term which a declaration is
  // generated for, as well as terminators) which have been used in a bit
  // asserted on frame, and have not been returned by GetPendingExps before.
  // all the pending exps must be in the specified frame, failing otherwise.
  // pushing/popping a context clears any remaining pending terms, and popping
  // a context shrinks the set of returned pending terms.
  void GetPendingExps(FrameId frame, Vector<Exp*> *exp_list);

  // get the pending terms which would be added for bit were it asserted,
  // regardless of whether those pending terms have been returned or not.
  void GetBitTerms(FrameId frame, Bit *bit, Vector<Exp*> *exp_list);

  // scans all pending bits and expands any ExpVal expressions. consumes other
  // pending terms for the frame.
  void ExpandPendingVal(FrameId frame);

  // is the conjunction of the added assertions satisfiable?
  // expired_result is the result to return if the alarm is expired.
  bool IsSatisfiable(bool expired_result = false);

  // attempt to add additional assertions to the solver forcing correct values
  // for the results of uninterpreted operations, while maintaining
  // satisfiability of the system. warns for any operation which
  // could not be fixed.
  void TryFixUninterpreted();

  // print the raw assignment generated by the underlying solver.
  // requires that the system is satisfiable.
  void PrintRawAssignment();

  // check that every bit asserted by this solver does indeed hold under
  // the satisfying assignment.
  void CheckAssignmentBits();

 public:
  // clear out all assertions from the context of this solver.
  void Clear();

  // push or pop the solver context. when the context is popped the solver
  // is restored to the state it was at when the corresponding push was
  // performed.
  void PushContext();
  void PopContext();

 public:
  // Asn functions are used to query the satisfying assignment.
  // the assignment can only be queried after calling PinAssign().

  // pins the solver's satisfying assignment such that subsequent Asn calls
  // will consistently fetch the same value for any term, including those
  // not mentioned in the currently asserted bits. requires that the solver
  // is satisfiable. new assertions cannot be added while the assignment
  // is pinned.
  void PinAssign();

  // unpin a satisfying assignment so that new assertions can be added.
  void UnpinAssign();

  // available when the solver's state is satisfiable. these can
  // only be called after IsSatisfiable() returns true.

  // check that the specified point is traversed within frame by the
  // satisfying assignment.
  void AsnCheckPointReached(FrameId frame, PPoint point);

  // get the outgoing edge from point which will be taken under
  // the assignment, NULL if the point has no outgoing edges. the point
  // must be visited by the assignment's path (i.e. AsnBitHolds()
  // is true for the guard at point). if required then the point *must*
  // have an outgoing edge in the assignment.
  PEdge* AsnEdgeTaken(FrameId frame, PPoint point, bool required = true);

  // store in res the value assigned to a bit or exp by the assignment.
  // return true if this value was determined by the assignment itself,
  // or false if it was chosen arbitrarily (if a declaration may have an
  // arbitrary value per the assignment, the same value is chosen wherever
  // the declaration is used).
  bool AsnBitValue(FrameId frame, Bit *bit, bool *res);
  bool AsnExpValue(FrameId frame, Exp *exp, mpz_t res);

  // get the assignment's value for a buffer offset.
  bool AsnOffset(FrameId frame, Exp *lval, Type *type, mpz_t res);

  // gets a reference on the exp from a guarded list of expressions chosen
  // by the satisfying assingment.
  Exp* AsnChooseExp(FrameId frame, const GuardExpVector &vals);

 public:
  // public debugging methods.

  // print the unsat core, or a facsimile thereof. requires that
  // the system is unsatisfiable and that we are running in DEBUG mode.
  // will abort the program after finishing.
  void PrintUnsatCore();

  // print the solver's representation for the specified values.
  // this excludes any side constraints that might have been generated
  // when translating the value.
  void PrintExp(FrameId frame, Exp *exp);
  void PrintBit(FrameId frame, Bit *bit);

 public:
  // public utility functions used while translating asserts.

  // extra state used for converting a bit or expression to the underlying
  // solver representation.
  struct ConvertState
  {
    // frame to use for uninterpreted terms.
    FrameId frame;

    // whether uninterpreted terms should be marked as pending.
    bool pending;

    // optional list to receive uninterpreted pending terms.
    Vector<Exp*> *exp_list;

    ConvertState(FrameId _frame, bool _pending,
                 Vector<Exp*> *_exp_list = NULL)
      : frame(_frame), pending(_pending), exp_list(_exp_list)
    {}
  };

  // marks the specified exp as pending if it was not previously returned
  // and if permitted by the conversion state.
  void AddPendingExp(const ConvertState &state, Exp *exp)
  {
    if (state.pending) {
      SlvExpr *pexpr = m_expr_handled_table.Lookup(state.frame, exp, false);
      if (pexpr == NULL)
        m_expr_pending_table.Lookup(state.frame, exp, true);
    }

    if (state.exp_list) {
      if (!state.exp_list->Contains(exp))
        state.exp_list->PushBack(exp);
    }
  }

  // whether there are any pending expressions in this solver.
  bool HasPendingExp()
  {
    return !m_expr_pending_table.IsEmpty();
  }

  // marks the specified exp as previously returned.
  void AddHandledExp(FrameId frame, Exp *exp)
  {
    m_expr_handled_table.Lookup(frame, exp, true);
  }

 private:
  // utility functions used while translating asserts.

  // add an assertion for the current context.
  void PushAssert(SlvExpr expr);

  // get the solver representation for a bit/exp.
  SlvExpr ConvertBit(const ConvertState &state, Bit *bit);
  SlvExpr ConvertExp(const ConvertState &state, Exp *exp);

  // helper for ConvertBit.
  SlvExpr RecursiveConvertBit(const ConvertState &state, Bit *bit,
                              bool revisit);

  // get the result of ConvertExp, coercing to an integral value
  // if necessary.
  SlvExpr ConvertExpIntegral(const ConvertState &state, Exp *exp);

  // check if exp should be converted as the difference of an absolute bound
  // or terminator offset and the offset of expression's target.
  void GetExpOffset(Exp *exp, Type **offset_type, Exp **offset_upper);

  // gets an expression for the offset of exp into its base buffer
  // according to the specified stride type.
  SlvExpr ConvertOffset(const ConvertState &state, Exp *lval, Type *type);

  // register a bound mentioned in bits for the specified frame.
  // frame is zero for absolute bounds. registering the bound adds assertions
  // relating the values for bounds on the same base with different strides.
  void RegisterBound(FrameId frame, ExpBound *bound, SlvExpr expr);

  // get or create a declaration for the specified expression. pexists is set
  // to indicate whether there was already a declaration.
  SlvDecl GetDeclaration(const ConvertState &state, Exp *exp, bool *pexists);

 private:

  // name to use printing for this solver.
  const char *m_name;

  // verbose output on the behavior of this solver.
  bool m_verbose;

  // external solver this is wrapping.
  BaseSolver *m_base;

  // table with the unconstrained variables from the underlying solver for
  // each uninterpreted expression accessed in the different solver frames.
  SolverDeclTable m_decl_table;

  // model assigning values to each declaration.
  SolverAssignment m_assign;

  // whether we have pinned and can query the satisfying assignment.
  bool m_assign_pinned;

  // whether the model reflects the state of the solver.
  bool m_have_assin;

  // table with all exps which can be returned by GetPendingExp.
  SolverExpTable m_expr_pending_table;

  // table with all exps which have already been returned by GetPendingExp.
  SolverExpTable m_expr_handled_table;

  // bits that have been asserted in each context.
  SolverBitTable m_asserted_bit_table;

  // if set, the constraints are known to be satisfiable. otherwise,
  // the constraints may or may not be satisfiable.
  bool m_satisfiable;

  // frames that have been handed out and associated block information.
  Vector<BlockMemory*> m_frames;

  // number of contexts that have been pushed.
  size_t m_context_count;

  // total time in usec that has been spent in this solver.
  uint64_t m_solve_time;

  // amount of time that has elapsed since this solver was created.
  Timer m_elapsed_timer;

  // list of all constraint tables within this solver.
  // ensure we push/pop/clear them all at the same time.
  Vector<ConstraintTable*> m_constraint_tables;

 public:
  // all constraint tables for this solver. these are public so they can
  // be accessed by the various constraint listeners themselves.
  // identity tables associate each key with a single identical entry.

  // identity table with all generated lvalues.
  ConstraintTable m_constraint_lvalue;

  // table mapping buffers to the bounds introduced for them.
  ConstraintTable m_constraint_bound;

  // table mapping buffers to the terminators introduced for them.
  ConstraintTable m_constraint_terminate;

  // table with every generated offset bound. one key for each type of offset.
  // (offsets are also included in m_constraint_bound).
  ConstraintTable m_constraint_offset;

  // table mapping buffers to the reads performed on them.
  ConstraintTable m_constraint_buffer_read;

  // identity table with all generated uninterpreted unops.
  ConstraintTable m_constraint_unint_unop;

  // identity table with all generated uninterpreted binops.
  ConstraintTable m_constraint_unint_binop;

  // table with all applications of uninterpreted binops for each frame.
  ConstraintTable m_constraint_combine_binop;

  // table with one step equalities between terms.
  ConstraintTable m_constraint_equal_step;

  // table with transitive equalities between terms.
  ConstraintTable m_constraint_equal_transitive;

  // for use by ConstraintTable constructor.
  void AddConstraintTable(ConstraintTable *table)
  {
    m_constraint_tables.PushBack(table);
  }

  // print all constraint tables in this solver.
  void PrintConstraintTables() const;
};

NAMESPACE_XGILL_END
