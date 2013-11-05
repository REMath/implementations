// sprint.cc
// code for sprint.h

#include "sprint.h"     // this module


void StructurePrinter::digStmt(Statement *s)
{
  // if this is a compound statement, traverse the elements;
  // otherwise, skip it entirely
  if (s->isS_compound()) {
    S_compound *c = s->asS_compound();
    FOREACH_ASTLIST_NC(Statement, c->stmts, iter) {
      iter.data()->traverse(*this);
    }
  }
}

bool StructurePrinter::visitTopForm(TopForm *tf)
{
  in(tf->loc);

  if (tf->isTF_func()) {
    // dig down into the body, b/c I don't want an extra level for
    // each function's body
    digStmt(tf->asTF_func()->f->body);

    out();

    // do *not* now go into the children again
    return false;
  }
  else {
    // automatically traverse children for other kinds of topforms
    return true;
  }
}

bool StructurePrinter::visitStatement(Statement *s)
{
  in(s->loc);

  ASTSWITCH(Statement, s) {
    ASTCASE(S_label, sl)
      digStmt(sl->s);

    ASTNEXT(S_case, sc)
      digStmt(sc->s);

    ASTNEXT(S_default, sd)
      digStmt(sd->s);

    ASTNEXT(S_if, si)
      digStmt(si->thenBranch);
      if (si->elseBranch->loc > si->loc) {
        digStmt(si->elseBranch);
      }
      else {
        // the else branch wasn't syntactically present
      }

    ASTNEXT(S_switch, ss)
      digStmt(ss->branches);

    ASTNEXT(S_while, sw)
      digStmt(sw->body);

    ASTNEXT(S_doWhile, sd)
      digStmt(sd->body);

    ASTNEXT(S_for, sf)
      digStmt(sf->body);

    ASTDEFAULT
      // those not listed above have their children automatically traversed
      return true;
      
    ASTENDCASE
  }

  // those that *are* listed above have already handled children
  out();
  return false;
}

ostream &StructurePrinter::ind()
{
  for (int i=0; i < depth; i++) {
    cout << "  ";
  }
  return cout;
}

bool StructurePrinter::in(SourceLoc loc)
{
  if (begin) {
    // I'm first in my parent's list
    cout << " {\n";
  }

  ind() << "begin=" << toString(loc);
  depth++;
  begin = true;
  return true;    // visit children
}

void StructurePrinter::out()
{
  depth--;
  if (begin) {
    // no children
    cout << "\n";
  }
  else {
    // finish child list
    ind() << "}\n";
  }
  begin = false;
}


void structurePrint(TranslationUnit *unit)
{
  StructurePrinter sp;
  unit->traverse(sp);
}


// EOF
