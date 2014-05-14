// main.cc            see license.txt for copyright and terms of use
// entry-point for Elsa-based Xgill frontend

#include <stdlib.h>       // exit, getenv, abort
#include <trace.h>        // traceAddSys
#include <parssppt.h>     // ParseTreeAndTokens, treeMain
#include <srcloc.h>       // SourceLocManager
#include <ckheap.h>       // malloc_stats
#include <cc_env.h>       // Env
#include <cc_ast.h>       // C++ AST (r)
#include <cc_ast_aux.h>   // class LoweredASTVisitor
#include <cc_lang.h>      // CCLang
#include <parsetables.h>  // ParseTables
#include <cc_print.h>     // PrintEnv
#include <cc.gr.gen.h>    // CCParse
#include <nonport.h>      // getMilliseconds
#include <ptreenode.h>    // PTreeNode
#include <ptreeact.h>     // ParseTreeLexer, ParseTreeActions
#include <sprint.h>       // structurePrint
#include <strtokp.h>      // StrtokParse
#include <smregexp.h>     // regexpMatch
#include <cc_elaborate.h> // ElabVisitor
#include <integrity.h>    // IntegrityVisitor
#if XML
  #include <main_astxmlparse.h>// astxmlparse
  #include <cc_type_xml.h>  // TypeToXml
#endif // XML

#include "xgill.h"
#include "xgill_file.h"

// for CheckSimplifications.
#include <solve/solver.h>

const char *USAGE = "ccxgill [options] file";

// hash used by manager for storing input files that still need
// to be processed.
#define FILE_WORKLIST_HASH "input_file_worklist"

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

Xgill::ConfigOption file_list(Xgill::CK_Flag, "file-list", NULL,
      "input file is a list of preprocessed files to parse\n"
  "      (for use with xmanager; this process only reads one file)");

Xgill::ConfigOption opt_trace(Xgill::CK_String, "trace", "",
  "':'-separated list of trace debug parameters");

Xgill::ConfigOption opt_strict(Xgill::CK_Flag, "strict", NULL,
  "fail if any parse or typechecking errors are encountered");

Xgill::ConfigOption opt_language(Xgill::CK_String, "language", "gnu",
      "language setting for parsing and type checking:\n"
  "      gnu: ANSI C/C++ with GNU extensions\n"
  "      ansi: ANSI C/C++"
);

Xgill::ConfigOption opt_errors(Xgill::CK_Flag, "print-errors", NULL,
      "print typechecking errors/warnings to stdout");

void ProcessTraceArg()
{
  char *val = (char*) opt_trace.StringValue();
  while (*val) {
    char *semi = strchr(val, ':');
    if (semi)
      *semi = 0;
    traceAddSys(val);
    if (semi) {
      *semi = ':';
      val = semi + 1;
    }
    else {
      break;
    }
  }
}

void doit(const char *inputFname, bool is_cpp)
{
  if (tracingSys("skipparse"))
    return;

  // I think this is more noise than signal at this point
  xBase::logExceptions = false;

  traceAddSys("progress");
  //traceAddSys("parse-tree");

  SourceLocManager mgr;
  if (tracingSys("nohashline"))
    sourceLocManager->useHashLines = false;

  // string table for storing parse tree identifiers
  StringTable strTable;

  // parsing language options
  CCLang lang;

  const char *language = opt_language.StringValue();
  if (strcmp(language, "gnu") == 0) {
    if (is_cpp) {
      lang.GNU_Cplusplus();
    }
    else {
      lang.ANSI_C89();
      lang.ANSI_C99_extensions();
      lang.GNU_C_extensions();
    }
  }
  else if (strcmp(language, "ansi") == 0) {
    if (is_cpp) {
      lang.ANSI_Cplusplus();
    }
    else {
      lang.ANSI_C89();
      lang.ANSI_C99_extensions();
    }
  }
  else {
    cout << "ERROR: Unknown setting for -lanugage" << endl;
    Xgill::Config::PrintUsage(USAGE);
    exit(2);
  }

  // --------------- parse --------------
  TranslationUnit *unit;

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

  // do the parse. this always succeeds.
  toplevelParse(tree, inputFname);

  int parseErrors = parseContext->errors + tree.errors;
  int parseWarnings = lexer->warnings + parseContext->warnings;

  if (!annotate.IsSpecified() || parseErrors || parseWarnings) {
    cout << "parsing results:" << endl
         << "  errors:   " << parseErrors << endl
         << "  warnings: " << parseWarnings << endl << flush;
  }

  if (parseErrors != 0 && opt_strict.IsSpecified())
    exit(2);

  // treeTop is a TranslationUnit pointer
  unit = (TranslationUnit*)treeTop;

  delete parseContext;
  delete tables;

  checkHeap();

  // print abstract syntax tree
  if (tracingSys("initAST")) {
    unit->debugPrint(cout, 0);
  }

  // ---------------- typecheck -----------------
  BasicTypeFactory tfac;

  Env env(strTable, lang, tfac, unit);

  if (annotate.IsSpecified())
    env.annotating = true;

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
  int numWarnings = env.errors.numWarnings();

  if (opt_errors.IsSpecified() || annotate.IsSpecified())
    env.errors.print(cout);
  else
    env.errors.printSummary(cout);

  if (!annotate.IsSpecified() || numErrors || numWarnings) {
    cout << "typechecking results:" << endl
         << "  errors:   " << numErrors << endl
         << "  warnings: " << numWarnings << endl << flush;
  }

  if (numErrors != 0 && opt_strict.IsSpecified())
    exit(2);

  // ----------------- elaboration ------------------
  if (lang.isCplusplus) {
    ElabVisitor vis(strTable, tfac, unit);
    unit->traverse(vis.loweredVisitor);
  }

  // print abstract syntax tree
  if (tracingSys("printAST")) {
    unit->debugPrint(cout, 0);
  }

  XgillSymbolVisitor symbol_visitor(env);
  unit->traverse(symbol_visitor);

  // transaction to query name and previous analysis information for
  // symbols in this compilation unit.
  Transaction *t = new Transaction();

  if (!annotate.IsSpecified()) {
    // get duplicate and previously analyzed information for each symbol
    // we found. don't do this for annotations, as each annotation file
    // has the same __name__/__value__ structure.

    SymbolDataFillTransaction csu_fill(t, "symbols_csu_hash");
    SymbolDataFillTransaction var_fill(t, "symbols_var_hash");
    csu_symbol_table.VisitEach(&csu_fill);
    var_symbol_table.VisitEach(&var_fill);

    SubmitTransaction(t);

    SymbolDataCheckTransaction symbol_check(t);
    csu_symbol_table.VisitEach(&symbol_check);
    var_symbol_table.VisitEach(&symbol_check);

    t->Clear();
  }

  SymbolDataProcess symbol_process(env, t);
  csu_symbol_table.VisitEach(&symbol_process);
  var_symbol_table.VisitEach(&symbol_process);

  if (annotate.IsSpecified()) {
    Assert(t->GetActionCount() == 0);
    ProcessAnnotation();
  }

  // submit any remaining database inserts from the process pass.
  if (t->GetActionCount() != 0)
    SubmitTransaction(t);

  delete t;
}

int main(int argc, char **argv)
{
  Xgill::Vector<const char*> files;
  bool parsed = Xgill::Config::Parse(argc, (const char**) argv, &files);
  if (!parsed || files.Size() != 1) {
    Xgill::Config::PrintUsage(USAGE);
    return 1;
  }

  // leaked references don't matter much since we can only do one file
  // at a time, and are hard to debug due to nondeterminism seemingly
  // introduced by Elsa.
#ifndef DEBUG
  Xgill::SimpleHashConsCounts();
#endif

  ProcessTraceArg();

  // DEBUG
  // Xgill::Solver::CheckSimplifications();

  Xgill::AnalysisPrepare();

  // scratch buffer if we need to store the filename.
  Xgill::Buffer file_name_buf;

  // get the file to read. set more_to_do depending on whether there
  // may be additional input files to process. this variable determines
  // our exit code.
  const char *file_name = NULL;
  bool more_to_do = false;

  if (file_list.IsSpecified()) {
    Transaction *t = new Transaction();

    if (!Xgill::IsAnalysisRemote()) {
      cout << "ERROR: -file-list can only be used with remote analysis" << endl;
      Xgill::Config::PrintUsage(USAGE);
      return 1;
    }

    // submit a transaction to see if the hash for the remaining input
    // files has already been created. if not we will have to do it ourself.

    size_t exist_result = t->MakeVariable(true);
    t->PushAction(Xgill::Backend::HashExists(t, FILE_WORKLIST_HASH, exist_result));

    SubmitTransaction(t);

    if (!t->LookupBoolean(exist_result)->IsTrue()) {
      // we need to read the file and fill in the hash contents.
      // make another transaction.

      t->Clear();

      // redo the call for the HashExists test, since there may be other
      // processes also trying to initialize the hashes. the form of
      // the transaction will be:
      // $existvar = HashExists(worklist_hash)
      // if !$existvar
      //   HashInsertKey(worklist_hash, file0)
      //   HashInsertKey(worklist_hash, file1)
      //   ...

      size_t exist_var = t->MakeVariable();
      TOperand *exist_arg = new TOperandVariable(t, exist_var);

      // test whose body is executed if we are the first to create the hash.
      TActionTest *test = new TActionTest(t, exist_arg, false);

      t->PushAction(Xgill::Backend::HashExists(t, FILE_WORKLIST_HASH, exist_var));
      t->PushAction(test);

      // buffer to store all the filenames.
      Xgill::Buffer *buf = new Xgill::Buffer();
      t->AddBuffer(buf);

      // read the input file into the filename buffer.
      ifstream file_in(files[0]);
      ReadInStream(file_in, buf);

      // tokenize the buffer based on the newlines.
      Xgill::Vector<char*> file_names;
      SplitBufferStrings(buf, '\n', &file_names);

      for (size_t find = 0; find < file_names.Size(); find++) {
        TOperand *key_arg = new TOperandString(t, file_names[find]);
        test->PushAction(
          Xgill::Backend::HashInsertKey(t, FILE_WORKLIST_HASH, key_arg));
      }

      SubmitTransaction(t);
    }

    t->Clear();

    // submit another transaction to get the name of the file we
    // will be processing.

    size_t key_result = t->MakeVariable(true);
    TOperand *key_arg = new TOperandVariable(t, key_result);

    t->PushAction(Xgill::Backend::HashChooseKey(t, FILE_WORKLIST_HASH, key_result));
    t->PushAction(Xgill::Backend::HashRemove(t, FILE_WORKLIST_HASH, key_arg));

    SubmitTransaction(t);

    TOperandString *key_name = t->LookupString(key_result);
    file_name_buf.Append(key_name->GetData(), key_name->GetDataLength());

    // done with the transaction.
    delete t;

    file_name = (const char*) file_name_buf.base;

    if (strlen(file_name) == 0) {
      // there are no more files to process. submit a terminating
      // transaction and exit with code 0.
      Xgill::SubmitTerminatingTransaction();
      Xgill::AnalysisFinish(0);
    }

    more_to_do = true;
  }
  else {
    file_name = files[0];
    more_to_do = false;
  }

  if (!annotate.IsSpecified())
    cout << "PARSE::Processing " << file_name << endl << flush;

  bool is_cpp = ProcessInputFileContents(file_name);

  try {
    doit(file_name, is_cpp);
  }
  catch (XUnimp &x) {
    HANDLER();
    cout << x << endl;
    abort();
  }
  catch (XFatal &x) {
    HANDLER();
    cout << x << endl;
    abort();
  }
  catch (xBase &x) {
    HANDLER();
    cout << x << endl;
    abort();
  }

  if (!more_to_do)
    Xgill::SubmitTerminatingTransaction();

  // cleanup and exit with code 1 if there is more to do, as we want this
  // process to be restarted.
  Xgill::ClearBlockCaches();
  Xgill::AnalysisFinish(more_to_do ? 1 : 0);
}
