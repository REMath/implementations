// sprint.h
// structure printer, for structural delta
// this module is experimental

#ifndef SPRINT_H
#define SPRINT_H

#include "cc_ast.h"     // C++ AST, visitor, etc.


// walk the AST, printing info about syntactic and
// static semantic structure
// (sm: This should not inherit from LoweredASTVisitor.)
// NOT Intended to be used with LoweredASTVisitor
class StructurePrinter : public ASTVisitor {
private:     // data
  // current syntactic nesting level; 0 means toplevel
  int depth;

  // true if we just began the current nesting level
  bool begin;

  // for each depth level, at what char offset did the current
  // entity begin?
  //ArrayStack<int> begins;

private:     // funcs
  ostream &ind();
  bool in(SourceLoc loc);
  void out();
  void digStmt(Statement *s);

public:      // funcs
  StructurePrinter()
    : depth(0),
      begin(false)
  {
    //begins.push(0);    // depth 0 starts at 0
  }

  virtual bool visitTopForm(TopForm *tf)      ;//{ return in(tf->loc); }
  virtual void postvisitTopForm(TopForm*)     { out(); }
  virtual bool visitStatement(Statement *s)   ;//{ return in(s->loc); }
  virtual void postvisitStatement(Statement*) { out(); }
  virtual bool visitMember(Member *m)         { return in(m->loc); }
  virtual void postvisitMember(Member*)       { out(); }
};
  

// convenient entry point
void structurePrint(TranslationUnit *unit);


#endif // SPRINT_H
