// cfg.h
// intraprocedural control flow graph over statements

#ifndef CFG_H
#define CFG_H

#include "array.h"        // ArrayStack<NextPtr>
#include "sobjlist.h"     // SObjList
#include "objstack.h"     // ObjStack
#include "sobjstack.h"    // SObjStack
#include "strmap.h"       // StringRefMap
#include "strtable.h"     // StringRef
#include "srcloc.h"       // SourceLoc

// can't just #include cc.ast.gen.h b/c that #includes this file
class Statement;
class S_break;
class S_label;
class S_goto;
class S_switch;
class Function;
class TranslationUnit;


// dsw: Design note: the graph that is built here is NOT the control
// flow graph!  It is only information additional to what is inherent
// in the AST that Statement::getSuccessors() needs to compute the
// control flow graph when asked; See the comment at the top of
// Statement::getSuccessors() in cfg.cc.  For example, an 'if'
// statement (S_if) never has an edge added to the start of its 'else'
// block because the fact that the 'else' (sometimes) follows the 'if'
// is inherent in the meaning of the AST.

// a 'next' pointer in the CFG, i.e. a pointer to a Statement
class NextPtr {
private:     // data
  // encoding is a Statement*, OR'd with 1 if it's a "continue" edge;
  // hopefully the compiler will be smart about representation and
  // calling convention, as both will be semantically equivalent to
  // how an ordinary 'long' is treated
  long p;

public:
  // construction, assignment
  NextPtr() : p(0) {}
  NextPtr(Statement *next, bool isContinue)
    : p((long)next | !!isContinue) {}
  NextPtr(NextPtr const &obj) : p(obj.p) {}
  NextPtr& operator= (NextPtr const &obj) { p = obj.p; return *this; }

  // comparison
  bool operator== (NextPtr const &obj) const { return p == obj.p; }
  bool operator!= (NextPtr const &obj) const { return p != obj.p; }

  // selection
  Statement *stmt() { return (Statement*)(p & ~1L); }
  bool cont() const { return (bool)(p & 1); }

  // like next()->kindLocString(), with a "(c)" appended if it's the
  // cont()==true half
  string asString();
};


// represent lists with a growable array/stack
typedef ArrayStack<NextPtr> NextPtrList;

// add another pointer to a list
inline void addNextPtr(NextPtrList &arr, NextPtr p)
  { arr.push(p); }

// iterate over such a thing
#define FOREACH_NEXTPTR(list, itervar) \
  for (ArrayStackIterNC<NextPtr> itervar(list); !itervar.isDone(); itervar.adv())


// environment for constructing an intraprocedural CFG
class CFGEnv {
  NO_OBJECT_COPIES(CFGEnv);

private:    // data
  ObjStack< SObjList<Statement> > pendingNexts;

  ObjStack< SObjList<S_break> > breaks;

  StringRefMap<S_label> labels;         // goto targets
  SObjStack<S_goto> gotos;              // goto sources (a set)

  SObjStack<S_switch> switches;
  SObjStack<Statement> loops;

public:     // data
  // count of errors found with e.g. goto/label correspondence
  int errors;

public:     // funcs
  CFGEnv();
  virtual ~CFGEnv();

  // report an error
  void err(SourceLoc loc, char const *str);

  // manipulate a stack of lists of nodes whose 'next' link
  // needs to be set
  void pushNexts();          // push an empty top
  void addPendingNext(Statement *source);
  void popNexts();           // merge two topmost frames
  void clearNexts();         // clear top
  void resolveNexts(NextPtr target);

  // manipulate a stack of lists of 'break' nodes whose 'next'
  // link needs to be set
  void pushBreaks();         // push empty top
  void addBreak(S_break *source);
  void popBreaks();          // resolve all at top, and pop frame

  // manipulate lists of sources and targets of gotos
  void addLabel(StringRef name, S_label *target);
  void addPendingGoto(S_goto *source);
  void resolveGotos();

  // maintain a stack of nested switch statements
  void pushSwitch(S_switch *sw);
  S_switch *getCurrentSwitch();
  void popSwitch();
  void connectEnclosingSwitch(Statement *stmt, char const *kind);

  // stack of nested loops
  void pushLoop(Statement *loop);
  Statement *getCurrentLoop();
  void popLoop();

  // check data structures for conditions which should hold between
  // funcs (if they do not, then there's a bug in the CFG algorithm,
  // not the user's code)
  void verifyFunctionEnd();
};


// given a function node annotated with CFG edges, return a list of
// all the CFG nodes, in reverse postorder w.r.t. some spanning tree
// (useful for initializing worklists in dataflow algorithms)
void reversePostorder(NextPtrList &order, Function *func);


// compute CFGs for all functions in a translation unit; return the
// number of CFG errors
int computeUnitCFG(TranslationUnit *unit);

// and for just one function, with an environment already made
void computeFunctionCFG(CFGEnv &env, Function *f);


#endif // CFG_H
