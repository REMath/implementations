// main.cc            see license.txt for copyright and terms of use
// entry-point module for a program that parses C++

#include <stdlib.h>       // exit, getenv, abort

#include "trace.h"        // traceAddSys
#include "parssppt.h"     // ParseTreeAndTokens, treeMain
#include "srcloc.h"       // SourceLocManager
#include "ckheap.h"       // malloc_stats
#include "cc_env.h"       // Env
#include "cc_ast.h"       // C++ AST (r)
#include "cc_ast_aux.h"   // class LoweredASTVisitor
#include "cc_lang.h"      // CCLang
#include "parsetables.h"  // ParseTables
#include "cc_print.h"     // PrintEnv
#include "cc.gr.gen.h"    // CCParse
#include "nonport.h"      // getMilliseconds
#include "ptreenode.h"    // PTreeNode
#include "ptreeact.h"     // ParseTreeLexer, ParseTreeActions
#include "sprint.h"       // structurePrint
#include "strtokp.h"      // StrtokParse
#include "smregexp.h"     // regexpMatch
#include "cc_elaborate.h" // ElabVisitor
#include "integrity.h"    // IntegrityVisitor
#if XML
  #include "main_astxmlparse.h"// astxmlparse
  #include "cc_type_xml.h"  // TypeToXml
#endif // XML

// don't know why I need this
//  class TypeToXml;

// little check: is it true that only global declarators
// ever have Declarator::type != Declarator::var->type?
// .. no, because it's true for class members too ..
// .. it's also true of arrays declared [] but then inited ..
// .. finally, it's true of parameters whose types get
//    normalized as per cppstd 8.3.5 para 3; I didn't include
//    that case below because there's no easy way to test for it ..
// Intended to be used with LoweredASTVisitor
class DeclTypeChecker : private ASTVisitor {
public:
  LoweredASTVisitor loweredVisitor; // use this as the argument for traverse()

  int instances;

public:
  DeclTypeChecker()
    : loweredVisitor(this)
    , instances(0)
  {}
  virtual ~DeclTypeChecker() {}

  virtual bool visitDeclarator(Declarator *obj);
};

bool DeclTypeChecker::visitDeclarator(Declarator *obj)
{
  if (obj->type != obj->var->type &&
      !(obj->var->flags & (DF_GLOBAL | DF_MEMBER)) &&
      !obj->type->isArrayType()) {
    instances++;
    cout << toString(obj->var->loc) << ": " << obj->var->name
         << " has type != var->type, but is not global or member or array\n";
  }
  return true;
}


// this scans the AST for E_variables, and writes down the locations
// to which they resolved; it's helpful for writing tests of name and
// overload resolution
class NameChecker : public ASTVisitor {
public:
  // accumulates the results
  stringBuilder sb;

public:
  NameChecker() {}

  virtual bool visitExpression(Expression *obj)
  {
    Variable *v = NULL;
    if (obj->isE_variable()) {
      v = obj->asE_variable()->var;
    }
    else if (obj->isE_fieldAcc()) {
      v = obj->asE_fieldAcc()->field;
    }
    
    // this output format is designed to minimize the effect of
    // changes to unrelated details
    if (v
        && !streq("__testOverload", v->name)
        && !streq("dummy",          v->name)
        && !streq("__other",        v->name) // "__other": for inserted elaboration code
        && !streq("this",           v->name) // dsw: not sure why "this" is showing up
        && !streq("operator=",      v->name) // an implicitly defined member of every class
        && v->name[0]!='~'                   // don't print dtors
        ) {
      sb << " " << v->name << "=" << sourceLocManager->getLine(v->loc);
    }

    return true;
  }
};


void if_malloc_stats()
{
  if (tracingSys("malloc_stats")) {
    malloc_stats();
  }
}


class SectionTimer {
  long start;
  long &elapsed;
  
public:
  SectionTimer(long &e) 
    : start(getMilliseconds()),
      elapsed(e)
  {}
  ~SectionTimer()
  {
    elapsed += getMilliseconds() - start;
  }
};

// print out type annotations for every ast node that has a type
class ToXmlASTVisitor_Types : public ToXmlASTVisitor {
//    ostream &out;                 // for the <Link/> tags
  TypeToXml &ttx;

  public:
  ToXmlASTVisitor_Types
    (TypeToXml &ttx0,
     ostream &out0,
     int &depth0,
     bool indent0 = false,
     bool ensureOneVisit0 = true)
      : ToXmlASTVisitor(out0, depth0, indent0, ensureOneVisit0)
      , ttx(ttx0)
  {}

  // Note that idempotency is handled in TypeToXml
  #define PRINT_ANNOT(A)   \
    if (A) {               \
      ttx.toXml(A); \
    }

  // this was part of the macro
//    printASTBiLink((void**)&(A), (A));

  // print the link between the ast node and the annotating node
//    void printASTBiLink(void **astField, void *annotation) {
//      out << "<__Link from=\"";
//      // this is not from an ast *node* but from the *field* of one
//      xmlPrintPointer(out, "FLD", astField);
//      out << "\" to=\"";
//      xmlPrintPointer(out, "TY", annotation);
//      out << "\"/>\n";
//    }

  // **** visit methods
  bool visitTypeSpecifier(TypeSpecifier *ts) {
    if (!ToXmlASTVisitor::visitTypeSpecifier(ts)) return false;
    if (ts->isTS_type()) {
      PRINT_ANNOT(ts->asTS_type()->type);
    } else if (ts->isTS_name()) {
      PRINT_ANNOT(ts->asTS_name()->var);
      PRINT_ANNOT(ts->asTS_name()->nondependentVar);
    } else if (ts->isTS_elaborated()) {
      PRINT_ANNOT(ts->asTS_elaborated()->atype);
    } else if (ts->isTS_classSpec()) {
      PRINT_ANNOT(ts->asTS_classSpec()->ctype);
    } else if (ts->isTS_enumSpec()) {
      PRINT_ANNOT(ts->asTS_enumSpec()->etype);
    }
    return true;
  }

  bool visitFunction(Function *f) {
    if (!ToXmlASTVisitor::visitFunction(f)) return false;
    PRINT_ANNOT(f->funcType);
    PRINT_ANNOT(f->receiver);
    return true;
  }

  bool visitMemberInit(MemberInit *memberInit) {
    if (!ToXmlASTVisitor::visitMemberInit(memberInit)) return false;
    PRINT_ANNOT(memberInit->member);
    PRINT_ANNOT(memberInit->base);
    PRINT_ANNOT(memberInit->ctorVar);
    return true;
  }

  bool visitBaseClassSpec(BaseClassSpec *bcs) {
    if (!ToXmlASTVisitor::visitBaseClassSpec(bcs)) return false;
    PRINT_ANNOT(bcs->type);
    return true;
  }

  bool visitDeclarator(Declarator *d) {
    if (!ToXmlASTVisitor::visitDeclarator(d)) return false;
    PRINT_ANNOT(d->var);
    PRINT_ANNOT(d->type);
    return true;
  }

  bool visitExpression(Expression *e) {
    if (!ToXmlASTVisitor::visitExpression(e)) return false;
    PRINT_ANNOT(e->type);
    if (e->isE_this()) {
      PRINT_ANNOT(e->asE_this()->receiver);
    } else if (e->isE_variable()) {
      PRINT_ANNOT(e->asE_variable()->var);
      PRINT_ANNOT(e->asE_variable()->nondependentVar);
    } else if (e->isE_constructor()) {
      PRINT_ANNOT(e->asE_constructor()->ctorVar);
    } else if (e->isE_fieldAcc()) {
      PRINT_ANNOT(e->asE_fieldAcc()->field);
    } else if (e->isE_new()) {
      PRINT_ANNOT(e->asE_new()->ctorVar);
    }
    return true;
  }

  #ifdef GNU_EXTENSION
  bool visitASTTypeof(ASTTypeof *a) {
    if (!ToXmlASTVisitor::visitASTTypeof(a)) return false;
    PRINT_ANNOT(a->type);
    return true;
  }
  #endif // GNU_EXTENSION

  bool visitPQName(PQName *pqn) {
    if (!ToXmlASTVisitor::visitPQName(pqn)) return false;
    if (pqn->isPQ_qualifier()) {
      PRINT_ANNOT(pqn->asPQ_qualifier()->qualifierVar);
      ttx.toXml(&(pqn->asPQ_qualifier()->sargs));
    } else if (pqn->isPQ_template()) {
      ttx.toXml(&(pqn->asPQ_template()->sargs));
    } else if (pqn->isPQ_variable()) {
      PRINT_ANNOT(pqn->asPQ_variable()->var);
    }
    return true;
  }

  bool visitEnumerator(Enumerator *e) {
    if (!ToXmlASTVisitor::visitEnumerator(e)) return false;
    PRINT_ANNOT(e->var);
    return true;
  }

  bool visitInitializer(Initializer *e) {
    if (!ToXmlASTVisitor::visitInitializer(e)) return false;
    if (e->isIN_ctor()) {
      PRINT_ANNOT(e->asIN_ctor()->ctorVar);
    }
    return true;
  }

  // FIX: TemplateParameter

  #undef PRINT_ANNOT
};


void handle_xBase(Env &env, xBase &x)
{
  // typically an assertion failure from the tchecker; catch it here
  // so we can print the errors, and something about the location
  env.errors.print(cout);
  cout << x << endl;
  cout << "Failure probably related to code near " << env.locStr() << endl;

  // print all the locations on the scope stack; this is sometimes
  // useful when the env.locStr refers to some template code that
  // was instantiated from somewhere else
  //
  // (unfortunately, env.instantiationLocStack isn't an option b/c
  // it will have been cleared by the automatic invocation of
  // destructors unwinding the stack...)
  cout << "current location stack:\n";
  cout << env.locationStackString();

  // I changed from using exit(4) here to using abort() because
  // that way the multitest.pl script can distinguish them; the
  // former is reserved for orderly exits, whereas signals (like
  // SIGABRT) mean that something went really wrong
  abort();
}


// this is a dumb way to organize argument processing...
char *myProcessArgs(int argc, char **argv, char const *additionalInfo)
{
  // remember program name
  char const *progName = argv[0];

  // process args
  while (argc >= 2) {
    if (traceProcessArg(argc, argv)) {
      continue;
    }
    else if (0==strcmp(argv[1], "-xc")) {
      // treat this as a synonym for "-tr c_lang"
      traceAddSys("c_lang");
      argv++;
      argc--;
    }
    else if (0==strcmp(argv[1], "-w")) {
      // synonym for -tr nowarnings
      traceAddSys("nowarnings");
      argv++;
      argc--;
    }
    else {
      break;     // didn't find any more options
    }
  }

  if (argc != 2) {
    cout << "usage: " << progName << " [options] input-file\n"
            "  options:\n"
            "    -tr <flags>:       turn on given tracing flags (comma-separated)\n"
         << (additionalInfo? additionalInfo : "");
    exit(argc==1? 0 : 2);    // error if any args supplied
  }

  return argv[1];
}


void doit(int argc, char **argv)
{
  // I think this is more noise than signal at this point
  xBase::logExceptions = false;

  traceAddSys("progress");
  //traceAddSys("parse-tree");

  if_malloc_stats();

  SourceLocManager mgr;

  // string table for storing parse tree identifiers
  StringTable strTable;

  // parsing language options
  CCLang lang;
  lang.GNU_Cplusplus();


  // ------------- process command-line arguments ---------
  char const *inputFname = myProcessArgs
    (argc, argv,
     "\n"
     "  general behavior flags:\n"
     "    c_lang             use C language rules (default is C++)\n"
     "    nohashline         ignore #line when reporting locations\n"
     "\n"
     "  options to stop after a certain stage:\n"
     "    stopAfterParse     stop after parsing\n"
     "    stopAfterTCheck    stop after typechecking\n"
     "    stopAfterElab      stop after semantic elaboration\n"
     "\n"
     "  output options:\n"
     "    parseTree          make a parse tree and print that, only\n"
     "    printAST           print AST after parsing\n"
     "    printTypedAST      print AST with type info\n"
     "    printElabAST       print AST after semantic elaboration\n"
     "    prettyPrint        echo input as pretty-printed C++\n"
     "    xmlPrintAST        print AST as XML\n"
     "\n"
     "  debugging output:\n"
     "    malloc_stats       print malloc stats every so often\n"
     "    env                print as variables are added to the environment\n"
     "    error              print as errors are accumulated\n"
     "    overload           print details of overload resolution\n"
     "\n"
     "  (grep in source for \"trace\" to find more obscure flags)\n"
     "");

  if (tracingSys("printAsML")) {
    Type::printAsML = true;
  }

  if (tracingSys("nohashline")) {
    sourceLocManager->useHashLines = false;
  }

  if (tracingSys("ansi")) {
    lang.ANSI_Cplusplus();
  }

  if (tracingSys("ansi_c")) {
    lang.ANSI_C89();
  }

  if (tracingSys("ansi_c99")) {
    lang.ANSI_C99();
  }

  if (tracingSys("c_lang")) {
    lang.GNU_C();
  }
  
  if (tracingSys("gnu_c89")) {
    lang.ANSI_C89();
    lang.GNU_C_extensions();
  }

  if (tracingSys("gnu_kandr_c_lang")) {
    lang.GNU_KandR_C();
    #ifndef KANDR_EXTENSION
      xfatal("gnu_kandr_c_lang option requires the K&R module (./configure -kandr=yes)");
    #endif
  }

  if (tracingSys("gnu2_kandr_c_lang")) {
    lang.GNU2_KandR_C();
    #ifndef KANDR_EXTENSION
      xfatal("gnu2_kandr_c_lang option requires the K&R module (./configure -kandr=yes)");
    #endif
  }
  
  if (tracingSys("test_xfatal")) {
    xfatal("this is a test error message");
  }

  if (tracingSys("msvcBugs")) {
    lang.MSVC_bug_compatibility();
  }

  if (!tracingSys("nowarnings")) {
    lang.enableAllWarnings();
  }

  if (tracingSys("templateDebug")) {
    // predefined set of tracing flags I've been using while debugging
    // the new templates implementation
    traceAddSys("template");
    traceAddSys("error");
    traceAddSys("scope");
    traceAddSys("templateParams");
    traceAddSys("templateXfer");
    traceAddSys("prettyPrint");
    traceAddSys("xmlPrintAST");
    traceAddSys("topform");
  }
  
  if (tracingSys("only_works_on_32bit") &&
      sizeof(long) != 4) {
    // we are running a regression test, and the testcase is known to
    // fail due to dependence on architecture parameters, so skip it
    cout << "skipping test b/c this is not a 32-bit architecture\n";
    exit(0);
  }

  // --------------- parse --------------
  TranslationUnit *unit;
  int parseWarnings = 0;
  long parseTime = 0;
  if (tracingSys("parseXml")) {
#if XML
    unit = astxmlparse(strTable, inputFname);
    if (!unit) return;
#else
    cout << "XML features are not compiled in" << endl;
    exit(1);
#endif // XML
  }
  else {
    SectionTimer timer(parseTime);
    SemanticValue treeTop;
    ParseTreeAndTokens tree(lang, treeTop, strTable, inputFname);
    
    // grab the lexer so we can check it for errors (damn this
    // 'tree' thing is stupid..)
    Lexer *lexer = dynamic_cast<Lexer*>(tree.lexer);
    xassert(lexer);

    CCParse *parseContext = new CCParse(strTable, lang);
    tree.userAct = parseContext;

    traceProgress(2) << "building parse tables from internal data\n";
    ParseTables *tables = parseContext->makeTables();
    tree.tables = tables;

    maybeUseTrivialActions(tree);

    if (tracingSys("parseTree")) {
      // make some helpful aliases
      LexerInterface *underLexer = tree.lexer;
      UserActions *underAct = parseContext;

      // replace the lexer and parser with parse-tree-building versions
      tree.lexer = new ParseTreeLexer(underLexer, underAct);
      tree.userAct = new ParseTreeActions(underAct, tables);

      // 'underLexer' and 'tree.userAct' will be leaked.. oh well
    }

    toplevelParse(tree, inputFname);

    // check for parse errors detected by the context class
    if (parseContext->errors || lexer->errors) {
      exit(2);
    }
    parseWarnings = lexer->warnings + parseContext->warnings;

    if (tracingSys("parseTree")) {
      // the 'treeTop' is actually a PTreeNode pointer; print the
      // tree and bail
      PTreeNode *ptn = (PTreeNode*)treeTop;
      ptn->printTree(cout, PTreeNode::PF_EXPAND);
      return;
    }

    // treeTop is a TranslationUnit pointer
    unit = (TranslationUnit*)treeTop;

    //unit->debugPrint(cout, 0);

    delete parseContext;
    delete tables;
  }

  checkHeap();

  // print abstract syntax tree
  if (tracingSys("printAST")) {
    unit->debugPrint(cout, 0);
  }

  //if (unit) {     // when "-tr trivialActions" it's NULL...
  //  cout << "ambiguous nodes: " << numAmbiguousNodes(unit) << endl;
  //}

  if (tracingSys("stopAfterParse")) {
    return;
  }


  // ---------------- typecheck -----------------
  BasicTypeFactory tfac;
  long tcheckTime = 0;
  if (tracingSys("no-typecheck")) {
    cout << "no-typecheck" << endl;
  } else {
    SectionTimer timer(tcheckTime);
    Env env(strTable, lang, tfac, unit);
    try {
      env.tcheckTranslationUnit(unit);
    }
    catch (XUnimp &x) {
      HANDLER();

      // relay to handler in main()
      cout << "in code near " << env.locStr() << ":\n";
      throw;
    }
    catch (xBase &x) {
      HANDLER();
      handle_xBase(env, x);
    }

    int numErrors = env.errors.numErrors();
    int numWarnings = env.errors.numWarnings() + parseWarnings;

    // do this now so that 'printTypedAST' will include CFG info
    #ifdef CFG_EXTENSION
    // A possible TODO is to do this right after each function is type
    // checked.  However, in the current design, that means physically
    // inserting code into Function::tcheck (ifdef'd of course).  A way
    // to do it better would be to have a general post-function-tcheck
    // interface that analyses could hook in to.  That could be augmented
    // by a parsing mode that parsed each function, analyzed it, and then
    // immediately discarded its AST.
    if (numErrors == 0) {
      numErrors += computeUnitCFG(unit);
    }
    #endif // CFG_EXTENSION

    // print abstract syntax tree annotated with types
    if (tracingSys("printTypedAST")) {
      unit->debugPrint(cout, 0);
    }

    // structural delta thing
    if (tracingSys("structure")) {
      structurePrint(unit);
    }

    if (numErrors==0 && tracingSys("secondTcheck")) {
      // this is useful to measure the cost of disambiguation, since
      // now the tree is entirely free of ambiguities
      traceProgress() << "beginning second tcheck...\n";
      Env env2(strTable, lang, tfac, unit);
      unit->tcheck(env2);
      traceProgress() << "end of second tcheck\n";
    }

    // print errors and warnings
    env.errors.print(cout);

    cout << "typechecking results:\n"
         << "  errors:   " << numErrors << "\n"
         << "  warnings: " << numWarnings << "\n";

    if (numErrors != 0) {
      exit(4);
    }

    // lookup diagnostic
    if (env.collectLookupResults.length()) {
      // scan AST
      NameChecker nc;
      nc.sb << "collectLookupResults";
      unit->traverse(nc);

      // compare to given text
      if (streq(env.collectLookupResults, nc.sb)) {
        // ok
      }
      else {
        cout << "collectLookupResults do not match:\n"
             << "  source: " << env.collectLookupResults << "\n"
             << "  tcheck: " << nc.sb << "\n"
             ;
        exit(4);
      }
    }
  }

  // ---------------- integrity checking ----------------
  long integrityTime = 0;
  {
    SectionTimer timer(integrityTime);

    // check AST integrity
    IntegrityVisitor ivis;
    unit->traverse(ivis);

    // check that the AST is a tree *and* that the lowered AST is a
    // tree; only do this *after* confirming that tcheck finished
    // without errors
    if (tracingSys("treeCheck")) {
      long start = getMilliseconds();
      LoweredIsTreeVisitor treeCheckVisitor;
      unit->traverse(treeCheckVisitor.loweredVisitor);
      traceProgress() << "done with tree check 1 ("
                      << (getMilliseconds() - start)
                      << " ms)\n";
    }

    // check an expected property of the annotated AST
    if (tracingSys("declTypeCheck") || getenv("declTypeCheck")) {
      DeclTypeChecker vis;
      unit->traverse(vis.loweredVisitor);
      cout << "instances of type != var->type: " << vis.instances << endl;
    }

    if (tracingSys("stopAfterTCheck")) {
      return;
    }
  }

  // ----------------- elaboration ------------------
  long elaborationTime = 0;
  if (!lang.isCplusplus || tracingSys("no-elaborate")) {
    cout << "no-elaborate" << endl;
  } 
  else {
    SectionTimer timer(elaborationTime);

    // do elaboration
    ElabVisitor vis(strTable, tfac, unit);

    // if we are going to pretty print, then we need to retain defunct children
    if (tracingSys("prettyPrint")
        // dsw: I don't know if this is right, but printing the xml
        // AST kind of resembles pretty-printing the AST; fix this if
        // it is wrong
        || tracingSys("xmlPrintAST")
        ) {
      vis.cloneDefunctChildren = true;
    }

    unit->traverse(vis.loweredVisitor);

    // print abstract syntax tree annotated with types
    if (tracingSys("printElabAST")) {
      unit->debugPrint(cout, 0);
    }
    if (tracingSys("stopAfterElab")) {
      return;
    }
  }

  // more integrity checking
  {
    SectionTimer timer(integrityTime);

    // check that the AST is a tree *and* that the lowered AST is a
    // tree (do this *after* elaboration!)
    if (tracingSys("treeCheck")) {
      long start = getMilliseconds();
      LoweredIsTreeVisitor treeCheckVisitor;
      unit->traverse(treeCheckVisitor.loweredVisitor);
      traceProgress() << "done with tree check 2 ("
                      << (getMilliseconds() - start)
                      << " ms)\n";
    }
  }

  // dsw: pretty printing
  if (tracingSys("prettyPrint")) {
    traceProgress() << "dsw pretty print...\n";
    OStreamOutStream out0(cout);
    CodeOutStream codeOut(out0);
    TypePrinterC typePrinter;
    PrintEnv env(typePrinter, &codeOut);
    cout << "---- START ----" << endl;
    cout << "// -*-c++-*-" << endl;
    unit->print(env);
    codeOut.finish();
    cout << "---- STOP ----" << endl;
    traceProgress() << "dsw pretty print... done\n";
  }

  // dsw: xml printing of the raw ast
  if (tracingSys("xmlPrintAST")) {
#if XML
    traceProgress() << "dsw xml print...\n";
    bool indent = tracingSys("xmlPrintAST-indent");
    int depth = 0;              // shared depth counter between printers
    cout << "---- START ----" << endl;
    if (tracingSys("xmlPrintAST-types")) {
      TypeToXml xmlTypeVis(cout, depth, indent);
      ToXmlASTVisitor_Types xmlVis_Types(xmlTypeVis, cout, depth, indent);
      xmlTypeVis.astVisitor = &xmlVis_Types;
      ASTVisitor *vis = &xmlVis_Types;
      LoweredASTVisitor loweredXmlVis(&xmlVis_Types); // might not be used
      if (tracingSys("xmlPrintAST-lowered")) {
        vis = &loweredXmlVis;
      }
      unit->traverse(*vis);
    } else {
      ToXmlASTVisitor xmlVis(cout, depth, indent);
      ASTVisitor *vis = &xmlVis;
      LoweredASTVisitor loweredXmlVis(&xmlVis); // might not be used
      if (tracingSys("xmlPrintAST-lowered")) {
        vis = &loweredXmlVis;
      }
      unit->traverse(*vis);
    }
    cout << endl;
    cout << "---- STOP ----" << endl;
    traceProgress() << "dsw xml print... done\n";
#else
    cout << "XML features are not compiled in" << endl;
    exit(1);
#endif // XML
  }

  // dsw: xml printing of the lowered ast
//    if (tracingSys("xmlPrintLoweredAST")) {
//  #if XML
//      traceProgress() << "dsw xml print...\n";
//      bool indent = tracingSys("xmlPrintLoweredAST-indent");
//      ToXmlASTVisitor xmlVis(cout, indent);
//      LoweredASTVisitor loweredXmlVis(&xmlVis);
//      // FIX: do type visitor
//      cout << "---- START ----" << endl;
//      unit->traverse(loweredXmlVis);
//      cout << endl;
//      cout << "---- STOP ----" << endl;
//      traceProgress() << "dsw xml print... done\n";
//  #else
//      cout << "XML features are not compiled in" << endl;
//      exit(1);
//  #endif // XML
//    }

  // test AST cloning
  if (tracingSys("testClone")) {
    TranslationUnit *u2 = unit->clone();

    if (tracingSys("cloneAST")) {
      cout << "------- cloned AST --------\n";
      u2->debugPrint(cout, 0);
    }

    if (tracingSys("cloneCheck")) {
      // dsw: I hope you intend that I should use the cloned TranslationUnit
      Env env3(strTable, lang, tfac, u2);
      u2->tcheck(env3);

      if (tracingSys("cloneTypedAST")) {
        cout << "------- cloned typed AST --------\n";
        u2->debugPrint(cout, 0);
      }

      if (tracingSys("clonePrint")) {
        OStreamOutStream out0(cout);
        CodeOutStream codeOut(out0);
        TypePrinterC typePrinter;
        PrintEnv penv(typePrinter, &codeOut);
        cout << "---- cloned pretty print ----" << endl;
        u2->print(penv);
        codeOut.finish();
      }
    }
  }

  // test debugPrint but send the output to /dev/null (basically just
  // make sure it doesn't segfault or abort)
  if (tracingSys("testDebugPrint")) {
    ofstream devnull("/dev/null");
    unit->debugPrint(devnull, 0);
  }

  cout << "parse=" << parseTime << "ms"
       << " tcheck=" << tcheckTime << "ms"
       << " integ=" << integrityTime << "ms"
       << " elab=" << elaborationTime << "ms"
       << "\n"
       ;

  //traceProgress() << "cleaning up...\n";

  //malloc_stats();

  // delete the tree
  // (currently this doesn't do very much because FakeLists are
  // non-owning, so I won't pretend it does)
  //delete unit;

  strTable.clear();

  //checkHeap();
  //malloc_stats();
}

int main(int argc, char **argv)
{
  try {
    doit(argc, argv);
  }
  catch (XUnimp &x) {
    HANDLER();
    cout << x << endl;

    // don't consider this the same as dying on an assertion failure;
    // I want to have tests in regrtest that are "expected" to fail
    // for the reason that they use unimplemented language features
    return 10;
  }
  catch (XFatal &x) {
    HANDLER();
    
    // similar to XUnimp
    cout << x << endl;
    return 10;
  }
  catch (xBase &x) {
    HANDLER();
    cout << x << endl;
    abort();
  }

  //malloc_stats();

  return 0;
}
