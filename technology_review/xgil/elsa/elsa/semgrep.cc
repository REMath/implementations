// semgrep.cc
// example Elsa application: semantic grep

#include <stdlib.h>       // exit, atoi

#include "parssppt.h"     // ParseTreeAndTokens
#include "srcloc.h"       // SourceLocManager
#include "cc_env.h"       // Env
#include "cc_ast.h"       // C++ AST (r)
#include "cc_lang.h"      // CCLang
#include "parsetables.h"  // ParseTables
#include "cc.gr.gen.h"    // CCParse
#include "strtokp.h"      // StrtokParse


// ---------------------- GrepVisitor ------------------------
class GrepVisitor : public ASTVisitor {
public:      // data
  // name of interest
  string name;
  int line;

public:      // funcs
  GrepVisitor(char const *n, int l)
    : name(n),
      line(l)
  {}
  virtual ~GrepVisitor() {}

  bool matches(Variable *var);
  void tryHit(Variable *var, SourceLoc refLoc, char const *use);

  virtual bool visitExpression(Expression *obj);
  virtual bool visitDeclarator(Declarator *obj);
};


bool GrepVisitor::matches(Variable *var)
{
  // compare line first for efficiency
  return line == sourceLocManager->getLine(var->loc) &&
         name.equals(var->name);
}

void GrepVisitor::tryHit(Variable *var, SourceLoc refLoc, char const *use)
{
  if (matches(var)) {
    cout << toString(refLoc) << ": " << use << "\n";
  }
}


bool GrepVisitor::visitExpression(Expression *obj)
{
  ASTSWITCH(Expression, obj) {
    ASTCASE(E_variable, e) {
      tryHit(e->var, e->name->loc, "use as variable");
    }
    ASTNEXT(E_fieldAcc, e) {
      tryHit(e->field, e->fieldName->loc, "use as field");
    }
    ASTENDCASED
  }

  return true;
}

bool GrepVisitor::visitDeclarator(Declarator *obj)
{
  // would like to be able to tell if it's a definition ...
  tryHit(obj->var, obj->decl->loc, "declaration");
  return true;
}


// ---------------------- main -------------------------
void doit(int argc, char **argv)
{
  xBase::logExceptions = false;

  SourceLocManager mgr;
  StringTable strTable;

  // parsing language options
  CCLang lang;
  lang.GNU_Cplusplus();


  // process command-line arguments
  if (argc != 4) {
    cout << "usage: " << argv[0] << " <name> <line> input.cc\n";
    return;
  }

  GrepVisitor grepv(argv[1], atoi(argv[2]));
  string inputFname = argv[3];

  //cout << "grepping for " << grepv.name
  //     << " on line " << grepv.line
  //     << " in " << inputFname << "\n";

  // parse+tcheck (TODO: make this more convenient)
  TranslationUnit *unit;
  {
    SemanticValue treeTop;
    ParseTreeAndTokens tree(lang, treeTop, strTable, inputFname.c_str());

    // grab the lexer so we can check it for errors (damn this
    // 'tree' thing is stupid..)
    Lexer *lexer = dynamic_cast<Lexer*>(tree.lexer);
    xassert(lexer);

    CCParse *parseContext = new CCParse(strTable, lang);
    tree.userAct = parseContext;

    ParseTables *tables = parseContext->makeTables();
    tree.tables = tables;

    // parse
    if (!toplevelParse(tree, inputFname.c_str())) {
      exit(2); // parse error
    }

    // check for parse errors
    if (parseContext->errors || lexer->errors) {
      exit(2);
    }

    // treeTop is a TranslationUnit pointer
    unit = (TranslationUnit*)treeTop;

    delete parseContext;
    delete tables;

    // tcheck
    BasicTypeFactory tfac;
    Env env(strTable, lang, tfac, unit);
    unit->tcheck(env);

    int numErrors = env.errors.numErrors();
    if (numErrors) {
      env.errors.print(cerr);
      cerr << numErrors << " errors\n";
      exit(4);
    }
  }

  // grep
  unit->traverse(grepv);
}

int main(int argc, char **argv)
{
  try {
    doit(argc, argv);
  }
  catch (xBase &x) {
    HANDLER();
    cout << x << endl;
    abort();
  }

  return 0;
}


// EOF
