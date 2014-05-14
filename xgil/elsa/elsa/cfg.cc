// cfg.cc
// code for cfg.h and cfg.ast

#include "cfg.h"           // this module
#include "cc_ast.h"        // C++ AST, including cfg.ast's contributions
#include "cc_ast_aux.h"    // class LoweredASTVisitor
#include "sobjset.h"       // SObjSet


// -------------------------- NextPtr ----------------------
string NextPtr::asString()
{
  return stringc << stmt()->kindLocString()
                 << (cont()? "(c)" : "");
}


// ---------------------- CFGEnv --------------------
CFGEnv::CFGEnv()
  : pendingNexts(),
    breaks(),
    labels(),
    gotos(),
    switches(),
    loops(),
    errors(0)
{
  // make empty top frames
  pushNexts();
  pushBreaks();
}

CFGEnv::~CFGEnv()
{}


void CFGEnv::err(SourceLoc loc, char const *str)
{
  cout << toString(loc) << ": " << str << endl;
}


// -------- nexts -------
void CFGEnv::pushNexts()
{
  pendingNexts.push(new SObjList<Statement>());
}

void CFGEnv::addPendingNext(Statement *source)
{
  pendingNexts.top()->prepend(source);
}

void CFGEnv::popNexts()
{
  SObjList<Statement> *top = pendingNexts.pop();
  pendingNexts.top()->concat(*top);    // empties 'top'
  delete top;
}

void CFGEnv::clearNexts()
{
  pendingNexts.top()->removeAll();
}

void CFGEnv::resolveNexts(NextPtr target)
{
  SMUTATE_EACH_OBJLIST(Statement, *(pendingNexts.top()), iter) {
    iter.data()->next = target;
  }
  clearNexts();
}


// -------- breaks --------
void CFGEnv::pushBreaks()
{
  breaks.push(new SObjList<S_break>());
}

void CFGEnv::addBreak(S_break *source)
{
  breaks.top()->prepend(source);     // O(n)
}

void CFGEnv::popBreaks()
{
  // all topmost breaks become pending nexts
  SMUTATE_EACH_OBJLIST(S_break, *(breaks.top()), iter) {
    addPendingNext(iter.data());
  }
  breaks.delPop();
}


// -------- labels --------
void CFGEnv::addLabel(StringRef name, S_label *target)
{
  labels.add(name, target);
}

void CFGEnv::addPendingGoto(S_goto *source)
{
  // sm: I'm not sure what I was thinking when I had 'gotos' as
  // a dictionary...
  
  gotos.push(source);
}

void CFGEnv::resolveGotos()
{
  // go over all the gotos and find their corresponding target
  while (gotos.isNotEmpty()) {
    S_goto *g = gotos.pop();
    S_label *target = labels.get(g->target);
    if (target) {
      g->next = NextPtr(target, false);
    }
    else {
      err(g->loc, stringc << "goto to undefined label: " << g->target);
    }
  }

  // empty the label dictionary (goto set already empty)
  labels.empty();
}


// -------- switches --------
void CFGEnv::pushSwitch(S_switch *sw)
{
  switches.push(sw);
}

S_switch *CFGEnv::getCurrentSwitch()
{
  return switches.top();
}

void CFGEnv::popSwitch()
{
  switches.pop();
}


// --------- loops ----------
void CFGEnv::pushLoop(Statement *loop)
{
  loops.push(loop);
}

Statement *CFGEnv::getCurrentLoop()
{
  return loops.top();
}

void CFGEnv::popLoop()
{
  loops.pop();
}


// -------- end --------
void CFGEnv::verifyFunctionEnd()
{
  xassert(pendingNexts.count() == 1);
  xassert(pendingNexts.top()->count() == 0);

  xassert(breaks.count() == 1);
  xassert(breaks.top()->count() == 0);

  xassert(labels.getNumEntries() == 0);
  xassert(gotos.isEmpty());

  xassert(switches.count() == 0);
  xassert(loops.count() == 0);
}


// ----------------------- Statement ---------------------
void Statement::computeCFG(CFGEnv &env)
{
  if (isS_for()) {
    // go immediately into 'init' so any pending 'next' pointers
    // point directly at the initializer; effectively, this makes the
    // system behave as if 'init' appeared syntactically just before
    // the "for" loop
    asS_for()->init->computeCFG(env);
  }

  // any pending 'next' pointers go here
  env.resolveNexts(NextPtr(this /*target*/, false /*continue*/));

  // my 'next' will go to whoever's (outer) tcheck is called next
  env.addPendingNext(this /*source*/);

  // do inner CFG computation
  icfg(env);
}


void S_skip::icfg(CFGEnv &env)
{}

void S_label::icfg(CFGEnv &env)
{
  env.addLabel(name, this);
  s->computeCFG(env);
}


void CFGEnv::connectEnclosingSwitch(Statement *stmt, char const *kind)
{
  S_switch *sw = getCurrentSwitch();
  if (!sw) {
    err(stmt->loc, stringc << kind << " can only appear in the context of a 'switch'");
  }
  else {
    sw->cases.append(stmt);
  }
}

void S_case::icfg(CFGEnv &env)
{
  env.connectEnclosingSwitch(this, "'case'");
  s->computeCFG(env);
}

void S_default::icfg(CFGEnv &env)
{
  env.connectEnclosingSwitch(this, "'default'");
  s->computeCFG(env);
}


void S_expr::icfg(CFGEnv &env)
{
  // this CFG does not model apparent flow of control present in
  // things like short-circuit evaluation of boolean expressions
}

void S_compound::icfg(CFGEnv &env)
{
  FOREACH_ASTLIST_NC(Statement, stmts, iter) {
    iter.data()->computeCFG(env);
  }
}

void S_if::icfg(CFGEnv &env)
{
  thenBranch->computeCFG(env);

  // any pending 'next's should not be resolved as pointing into
  // the 'else' clause, but instead as pointing at whatever follows
  // the entire 'if' statement
  env.pushNexts();

  elseBranch->computeCFG(env);

  // merge current pending nexts with those saved above
  env.popNexts();
}

void S_switch::icfg(CFGEnv &env)
{
  // existing 'break's must be postponed
  env.pushBreaks();

  // any occurrences of 'case' will be relative to this switch
  env.pushSwitch(this);
  branches->computeCFG(env);
  env.popSwitch();

  // any 'break's found will resolve to whatever comes next
  env.popBreaks();
}


static void icfgLoop(CFGEnv &env, Statement *loop, Statement *body)
{
  // existing 'break's must be postponed
  env.pushBreaks();

  // any occurrences of 'continue' will be relative to this loop
  env.pushLoop(loop);
  body->computeCFG(env);
  env.popLoop();

  // the body continues back into this loop
  env.resolveNexts(NextPtr(loop /*target*/, true /*continue*/));

  // any previous 'break's will resolve to whatever comes next
  env.popBreaks();

  // I want the loop's 'next' to point to what comes after; right now
  // it points at the body (if anywhere; see S_for), and this will
  // change it
  env.addPendingNext(loop /*source*/);
}

void S_while::icfg(CFGEnv &env)
{
  icfgLoop(env, this, body);
}

void S_doWhile::icfg(CFGEnv &env)
{
  icfgLoop(env, this, body);
}

void S_for::icfg(CFGEnv &env)
{
  icfgLoop(env, this, body);
}


void S_break::icfg(CFGEnv &env)
{
  // add myself to the list of active breaks
  env.addBreak(this);
}

void S_continue::icfg(CFGEnv &env)
{
  Statement *loop = env.getCurrentLoop();
  if (!loop) {
    env.err(loc, "'continue' can only occur in the scope of a loop");
  }
  else {
    // take myself off the list of pending nexts
    env.clearNexts();

    // point my next at the loop
    next = NextPtr(loop, true /*continue*/);
  }
}

void S_return::icfg(CFGEnv &env)
{
  // ensure my 'next' is null
  env.clearNexts();
  xassert(next.stmt() == NULL);
}


void S_goto::icfg(CFGEnv &env)
{
  env.addPendingGoto(this);
}


void S_decl::icfg(CFGEnv &env)
{}


void S_try::icfg(CFGEnv &env)
{ 
  // control flows into the body
  body->computeCFG(env);
  
  // but, it could spontaneously arrive at any of the handlers..
  // hmm.. that raises at least two issues:
  //   - control can transfer away from any statement at any time,
  //     because of a thrown exception; so all claims as to what
  //     statement is "next" are conditional upon no exceptions
  //   - I need a way to regard handlers as origins of the CFG, but
  //     which can only be reached after the try block has entered,
  //     and not after it has exited.. I have no idea how to do that
  //     without being dramatically conservative (forget about the
  //     time constraint, for example)
  FAKELIST_FOREACH(Handler, handlers, h) {
    // save any pending 'next's until after the handler
    env.pushNexts();

    // treat the handler as a CFG origin
    h->body->computeCFG(env);

    // merge resulting 'next's with those we saved
    env.popNexts();
  }

  // now, we've merged the 'try' body 'next's with all of those from
  // the handlers, and will point all of them at whatever poor,
  // unsuspecting statement might come next
}


void S_asm::icfg(CFGEnv &env)
{}

void S_namespaceDecl::icfg(CFGEnv &env)
{}


// ------------------ Statement::getSuccessors ----------------
// add it if it's not NULL
static void addNextPtrIf(NextPtrList &arr, NextPtr p)
{
  if (p.stmt()) {
    addNextPtr(arr, p);
  }
}

// this function interprets the 'next' field, plus any other control
// flow intrinsic to the statement, to find out which statements might
// receive control flow after this one
void Statement::getSuccessors(NextPtrList &dest, bool isContinue)
{
  ASTSWITCH(Statement, this) {
    ASTCASE(S_if, i)
      // the 'next' field is ignored since it always points at
      // the 'then' branch anyway
      addNextPtr(dest, NextPtr(i->thenBranch, false));
      addNextPtr(dest, NextPtr(i->elseBranch, false));

    ASTNEXT(S_switch, s)
      SFOREACH_OBJLIST_NC(Statement, s->cases, iter) {
        addNextPtr(dest, NextPtr(iter.data(), false));
      }

    ASTNEXT(S_while, w)
      addNextPtrIf(dest, next);
      addNextPtr(dest, NextPtr(w->body, false));

    ASTNEXT(S_doWhile, d)
      if (isContinue) {
        // continue jumps to conditional, so it could exit the loop
        addNextPtrIf(dest, next);
      }
      // either way, doing the body is an option
      addNextPtr(dest, NextPtr(d->body, false));

    ASTNEXT(S_for, f)
      // though the semantics of choosing which expressions get
      // evaluated are different depending on 'isContinue', the
      // statement-level control flow options are the same
      addNextPtrIf(dest, next);
      addNextPtr(dest, NextPtr(f->body, false));

    ASTDEFAULT
      // for most statements, there is only one control flow option
      addNextPtrIf(dest, next);

    ASTENDCASE
  }
}


static bool contains(NextPtrList &arr, NextPtr p)
{
  for (int i=0; i < arr.length(); i++) {
    if (arr[i] == p) {
      return true;
    }
  }
  return false;   // not found
}

string Statement::successorsToString() const
{
  // getSuccessors() is not declared const because it returns pointers
  // that are themselves not const.. but that capability won't be
  // abused in this function, so I'll cast away constness so I can
  // call that function
  Statement *ths = const_cast<Statement*>(this);

  NextPtrList succNoCont;
  ths->getSuccessors(succNoCont, false);

  NextPtrList succYesCont;
  ths->getSuccessors(succYesCont, true);

  stringBuilder sb;
  sb << "{";

  for (int i=0; i < succYesCont.length(); i++) {
    NextPtr np = succYesCont[i];

    // a leading "(c)" means the successor edge is only present when
    // this node is reached via continue; a trailing "(c)" means that
    // successor is itself a continue edge; the algorithm assumes
    // that 'succYesCont' is a superset of 'succNoCont'
    sb << (contains(succNoCont, np)? " " : " (c)")
       << np.stmt()->lineColString()
       << (np.cont()? "(c)" : "");
  }

  sb << " }";
  return sb;
}


// ------------------- reversePostorder ---------------
// DFS from 'node', having arrived at node with 'isContinue'
// disposition; 'seen' is those nodes either currently being
// considered somewhere in the call chain ("gray"), or else finished
// entirely ("black"), and 'seenCont' is the same thing but for the
// continue==true halves of the nodes
static
void rp_dfs(NextPtrList &order, NextPtr node,
            SObjSet<Statement*> &seen, SObjSet<Statement*> &seenCont)
{
  // we're now considering 'node'; did we arrive via continue?
  (node.cont()? seenCont : seen).add(node.stmt());     // C++ generalized lvalue!

  // consider each of this node's successors
  NextPtrList successors;
  node.stmt()->getSuccessors(successors, node.cont());

  for (int i=0; i < successors.length(); i++) {
    NextPtr succ = successors[i];

    if ((succ.cont()? seenCont : seen).contains(succ.stmt())) {
      // we're already considering, or have already considered, this node;
      // do nothing with it
    }
    else {
      // visit this new child
      rp_dfs(order, succ, seen, seenCont);
    }
  }

  // since we're finished with this node, we append it to compute the
  // postorder
  order.push(node);
}


void reversePostorder(NextPtrList &order, Function *func)
{
  xassert(order.isEmpty());

  // DFS from the function start, computing the spanning tree implicitly,
  // and the postorder explicitly
  SObjSet<Statement*> seen, seenCont;
  rp_dfs(order, NextPtr(func->body, false /*isContinue*/), seen, seenCont);
  
  // reverse the list
  int low=0, high=order.length()-1;
  while (low < high) {
    NextPtr temp = order[low];
    order[low] = order[high];
    order[high] = temp;
    low++;
    high--;
  }
}


// --------------------- computeCFG -------------------
// Intended to be used with LoweredASTVisitor
class CFGVisitor : private ASTVisitor {
public:
  LoweredASTVisitor loweredVisitor; // use this as the argument for traverse()

private:
  CFGEnv &env;

public:
  CFGVisitor(CFGEnv &e)
    : loweredVisitor(this)
    , env(e)
  {}
  virtual ~CFGVisitor() {}

  virtual bool visitFunction(Function *obj);
};

bool CFGVisitor::visitFunction(Function *obj)
{
  computeFunctionCFG(env, obj);

  return true;     // visit children (it's possible to nest functions inside local classes)
}

void computeFunctionCFG(CFGEnv &env, Function *f)
{
  f->body->computeCFG(env);

  env.resolveGotos();
  env.resolveNexts(NextPtr(NULL /*target*/, false /*isContinue*/));

  env.verifyFunctionEnd();
}

int computeUnitCFG(TranslationUnit *unit)
{
  CFGEnv env;
  CFGVisitor vis(env);
  unit->traverse(vis.loweredVisitor);

  // plan for supporting GNU statement-expression: use the visitor to
  // find the statement-expressions, and treat them as relatively
  // isolated pieces (push & pop the environment) of the CFG, but
  // still in the context of the function (for gotos, etc.)
  
  return env.errors;
}


// EOF
