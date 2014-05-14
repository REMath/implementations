// parsetables.h            see license.txt for copyright and terms of use
// ParseTables, a class to contain the tables need by the
// LR/GLR parsing algorithm

#ifndef PARSETABLES_H
#define PARSETABLES_H

#include "array.h"        // ArrayStack
#include "glrconfig.h"    // compression options
#include "str.h"          // string


class Flatten;            // flatten.h
class EmitCode;           // emitcode.h
class Symbol;             // grammar.h
class Bit2d;              // bit2d.h


// integer id for an item-set DFA state; I'm using an 'enum' to
// prevent any other integers from silently flowing into it
enum StateId { STATE_INVALID=-1 };

inline ostream& operator<< (ostream &os, StateId id)
  { return os << (int)id; }

// encodes an action in 'action' table; see 'actionTable'

// each entry is one of:
//   +N+1, 0 <= N < numStates:         shift, and go to state N
//   -N-1, 0 <= N < numProds:          reduce using production N
//   numStates+N+1, 0 <= N < numAmbig: ambiguous, use ambigAction N
//   0:                                error
// (there is no 'accept', acceptance is handled outside this table)
typedef signed short ActionEntry;
#define errorActionEntry ((ActionEntry)0)

// encodes a destination state in 'gotoTable'

// entry is the to go to after shifting the nonterminal
typedef unsigned short GotoEntry;
#define errorGotoEntry ((GotoEntry)~0)

// encodes an action in 'error' table; see 'errorTable'

// each entry is one of:
//   0:   cannot recover (if one entry is 0, entire row is 0)
//   1:   consume next token
//   2:   stop consuming and push error token onto stack
typedef signed short ErrorEntry;
#define missingErrorEntry ((ErrorEntry)0)
#define advanceErrorEntry ((ErrorEntry)1)
#define shiftErrorEntry   ((ErrorEntry)2)

// name a terminal using an index
typedef unsigned char TermIndex;

// name a nonterminal using an index
typedef unsigned short NtIndex;

// name a production using an index
typedef unsigned short ProdIndex;


// encodes either terminal index N (as N+1) or
// nonterminal index N (as -N-1), or 0 for no-symbol
typedef signed short SymbolId;
inline bool symIsTerm(SymbolId id) { return id > 0; }
inline int symAsTerm(SymbolId id) { return id-1; }
inline bool symIsNonterm(SymbolId id) { return id < 0; }
inline NtIndex symAsNonterm(SymbolId id) { return (NtIndex)(-(id+1)); }
SymbolId encodeSymbolId(Symbol const *sym);       // gramanl.cc


// assign, but check for truncation
template <class DEST, class SRC>
inline void checkAssign(DEST &d, SRC s)
{
  d = (DEST)s;
  xassert(d == s);
}


// the parse tables are the traditional action/goto, plus the list
// of ambiguous actions, plus any more auxilliary tables useful during
// run-time parsing
class ParseTables {
private:    // types
  // data about an intermediate state of parse table construction;
  // once the table is finished, this data gets consolidated into the
  // actual tables, and then thrown away
  class TempData {
  public:   // data
    // nascent ambigTable
    ArrayStack<ActionEntry> ambigTable;

    // nascent bigProductionList
    ArrayStack<ProdIndex> bigProductionList;
    
    // nascent productionsForState, except using integer offsets from
    // start of 'bigProductionList' instead of direct pointers into it
    ArrayStack<int> productionsForState;

    // nascent versions of ambig tables, again with integer offsets
    ArrayStack<int> ambigStateTable;

  public:   // funcs
    TempData(int numStates);
    ~TempData();
  };

public:     // types
  // per-production info
  struct ProdInfo {
    unsigned char rhsLen;                // # of RHS symbols
    NtIndex lhsIndex;                    // 'ntIndex' of LHS
  };

public: // data
  // when this is false, all of the below "(owner*)" annotations are
  // actually "(serf)", i.e. this object does *not* own any of the
  // tables (see emitConstructionCode())
  bool owning;

  // non-NULL during construction
  TempData *temp;                        // (nullable owner)

  // # terminals, nonterminals in grammar
  int numTerms;
  int numNonterms;

  // # of parse states
  int numStates;

  // # of productions in the grammar
  int numProds;

  // number of the special error terminal
  int errorTerm;

  // action table, indexed by (state*actionCols + lookahead)
  int actionCols;
  int actionRows;
  ActionEntry *actionTable;              // (owner*)

  // goto table, indexed by (state*gotoCols + nontermId)
  int gotoCols;
  int gotoRows;
  GotoEntry *gotoTable;                  // (owner*)

  // error recovery table, indexed by (state *errorCols + lookahead)
  int errorCols;
  int errorRows;
  ErrorEntry *errorTable;                // (owner*)

  // map production id to information about that production
  ProdInfo *prodInfo;                    // (owner*)

  // map a state id to the symbol (terminal or nonterminal) which is
  // shifted to arrive at that state
  SymbolId *stateSymbol;                 // (owner*)

  // ambiguous actions: one big list, for allocation purposes; then
  // the actions encode indices into this table; the first indexed
  // entry gives the # of actions, and is followed by that many
  // actions, each interpreted the same way ordinary 'actionTable'
  // entries are
  int ambigTableSize;
  ActionEntry *ambigTable;               // (nullable owner*)

  // total order on nonterminals for use in choosing which to
  // reduce to in the RWL algorithm; index into this using a
  // nonterminal index, and it yields the ordinal for that
  // nonterminal (so these aren't really NtIndex's, but they're
  // exactly as wide, so I use NtIndex anyway)
  //
  // The order is consistent with the requirement that if
  //   A ->+ B
  // then B will be earlier in the order (assuming acyclicity).
  // That way, we'll do all reductions to B before any to A (for
  // reductions spanning the same set of ground terminals), and
  // therefore will merge all alternatives for B before reducing
  // any of them to A.
  NtIndex *nontermOrder;                 // (owner*)

public:     // data
  // These are public because if they weren't, I'd just have a stupid
  // getter/setter pattern that exposes them anyway.

  // start state id
  StateId startState;

  // index of the production which will finish a parse; it's the
  // final reduction executed
  int finalProductionIndex;

public:    // funcs
  void alloc(int numTerms, int numNonterms, int numStates, int numProds,
             int errorTerm, StateId start, int finalProd);

  // index tables

  ActionEntry &actionEntry(StateId stateId, int termId)
    { return actionTable[stateId*actionCols + termId]; }
  int actionTableSize() const
    { return actionRows * actionCols; }

  GotoEntry &gotoEntry(StateId stateId, int nontermId)
    { return gotoTable[stateId*gotoCols + nontermId]; }
  int gotoTableSize() const
    { return gotoRows * gotoCols; }

  ErrorEntry &errorEntry(StateId stateId, int termId)
    { return errorTable[stateId*errorCols + termId]; }
  int errorTableSize() const
    { return errorRows * errorCols; }

  void appendAmbig(ArrayStack<ActionEntry> const &set);
  bool compareAmbig(ArrayStack<ActionEntry> const &set, int startIndex);

protected:  // funcs
  // the idea is that 'emitConstructionCode' will emit code that
  // defines a subclass of 'ParseTables'; that's why so many of the
  // data members are protected: the subclass can then access them
  // directly, which is very convenient when trying to construct the
  // tables from static data
  ParseTables(bool owning);    // only legal when owning==false

public:     // funcs
  ParseTables(int numTerms, int numNonterms, int numStates, int numProds,
              int errorTerm, StateId start, int finalProd);
  ~ParseTables();

  // simple queries
  int getNumTerms() const { return numTerms; }
  int getNumNonterms() const { return numNonterms; }
  int getNumStates() const { return numStates; }
  int getNumProds() const { return numProds; }

  // finish construction; do this before emitting code
  void finishTables();

  // write the tables out as C++ source that can be compiled into
  // the program that will ultimately do the parsing
  void emitConstructionCode(EmitCode &out, rostring className, rostring funcName);

  // this does the same thing for ML, and is implemented in genml.cc
  void emitMLConstructionCode(EmitCode &out, rostring className, rostring funcName);

  void setActionEntry(StateId stateId, int termId, ActionEntry act)
    { actionEntry(stateId, termId) = act; }
  void setGotoEntry(StateId stateId, int nontermId, GotoEntry got)
    { gotoEntry(stateId, nontermId) = got; }
  void setErrorEntry(StateId stateId, int termId, ErrorEntry err)
    { errorEntry(stateId, termId) = err; }

  // encode actions
  ActionEntry encodeShift(StateId destState);
  ActionEntry encodeReduce(int prodId);
  ActionEntry encodeAmbig(ArrayStack<ActionEntry> const &set);
  ActionEntry encodeError() const;
  ActionEntry validateAction(int code) const;

  // encode gotos
  GotoEntry encodeGoto(StateId stateId, int shiftedNontermId) const;
  GotoEntry encodeGotoError() const
    { return errorGotoEntry; }
  GotoEntry validateGoto(int code) const;

  // misc
  void setProdInfo(int prodId, int rhsLen, int ntIndex) {
    checkAssign(prodInfo[prodId].rhsLen, rhsLen);
    checkAssign(prodInfo[prodId].lhsIndex, ntIndex);
  }
  void setStateSymbol(StateId state, SymbolId sym) {
    stateSymbol[state] = sym;
  }
  NtIndex *getWritableNontermOrder() {
    // expose this directly, due to the way the algorithm that
    // computes it is written
    return nontermOrder;
  }

  // -------------------- table queries ---------------------------
  // return true if the action is an error
  bool actionEntryIsError(StateId stateId, int termId) {
    return isErrorAction(actionEntry(stateId, termId));
  }

  // query action table, without checking the error bitmap
  ActionEntry getActionEntry_noError(StateId stateId, int termId) {
    return actionEntry(stateId, termId);
  }

  // query the action table, yielding an action that might be
  // an error action
  ActionEntry getActionEntry(StateId stateId, int termId) {
    return getActionEntry_noError(stateId, termId);
  }

  // decode actions
  bool isShiftAction(ActionEntry code) const
    { return code > 0 && code <= numStates; }
  static StateId decodeShift(ActionEntry code, int /*shiftedTerminal*/)
    { return (StateId)(code-1); }
  static bool isReduceAction(ActionEntry code)
    { return code < 0; }
  static int decodeReduce(ActionEntry code, StateId /*inState*/)
    { return -(code+1); }
  static bool isErrorAction(ActionEntry code)
    { return code == 0; }

  // ambigAction is only other choice; this yields a pointer to
  // an array of actions, the first of which says how many actions
  // there are
  ActionEntry *decodeAmbigAction(ActionEntry code, StateId /*inState*/) const
    { return ambigTable + (code-1-numStates); }

  // decode gotos
  GotoEntry getGotoEntry(StateId stateId, int nontermId) {
    return gotoEntry(stateId, nontermId);
  }

  bool isErrorGoto(GotoEntry code)
    { return code == errorGotoEntry; }

  StateId decodeGoto(GotoEntry code, int shiftedNonterminal) {
    return (StateId)code;
  }

  // nonterminal order
  int nontermOrderSize() const
    { return numNonterms; }
  NtIndex getNontermOrdinal(NtIndex idx) const
    { return nontermOrder[idx]; }

  // misc
  ProdInfo const &getProdInfo(int prodIndex) const
    { return prodInfo[prodIndex]; }
  int getStateSymbol(StateId id) const
    { return stateSymbol[id]; }
};


// NOTE: At one point (before 7/27/03), I had the ability to read and
// write parse tables to files, *not* using the C++ compiler to store
// tables as static data.  I removed it because I wasn't using it, and
// it was hindering table evolution.  But as the tables stabilize
// again, if the need arises, one could go get (from CVS) the code
// that did it and fix it up to work again.


#endif // PARSETABLES_H
