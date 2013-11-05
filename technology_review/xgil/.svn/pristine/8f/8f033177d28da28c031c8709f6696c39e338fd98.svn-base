// smin.cc
// structural minimizer

#include "test.h"           // ARGS_MAIN
#include "smin.h"           // this module
#include "trace.h"          // TRACE_ARGS

#include <stdlib.h>         // system
#include <sys/types.h>      // ?
#include <sys/wait.h>       // W* macros for interpreting exit status


// ------------------ XCtrlC -------------------
XCtrlC::XCtrlC()
  : xBase("ctrl-c")
{}

XCtrlC::XCtrlC(XCtrlC const &obj)
  : xBase(obj)
{}

XCtrlC::~XCtrlC()
{}


// ----------------- Minimizer -----------------
Minimizer::Minimizer()
  : sourceFname(),
    testProg(),
    source(10 /*hint*/),
    tree(NULL),
    results(),
    passingTests(0),
    failingTests(0),
    cachedTests(0),
    testInputSum(0)
{}

Minimizer::~Minimizer()
{
  if (tree) {
    delete tree;
  }
}


void setIrrelevant(IPTree &t, int offset)
{
  Node *n = t.query(offset);
  if (n) {
    n->rel = R_IRRELEVANT;
  }
}


int system(rostring s)
{
  return system(toCStr(s));
}


VariantResult Minimizer::runTest()
{
  int code = system(stringc << testProg << " \'" << sourceFname << "\'");
  if (WIFSIGNALED(code) && WTERMSIG(code) == SIGINT) {
    XCtrlC x;
    THROW(x);
  }
  
  if (code == 0) {
    cout << "p";
    flush(cout);
    passingTests++;
    return VR_PASSED;
  }
  else {
    cout << ".";
    flush(cout);
    failingTests++;
    return VR_FAILED;
  }
}


bool Minimizer::outerRunTest(int &size, Node *n, Relevance rel)
{
  // temporarily set n->rel
  Relevance origRel = n->rel;
  n->rel = rel;

  VariantCursor cursor = write(size);
  if (!cursor->data) {
    // this variant has not already been tried, so test it
    testInputSum += size;
    try {
      cursor->data = runTest();
    }
    catch (XCtrlC &) {
      // restore the relevance guess
      HANDLER();
      n->rel = origRel;
      throw;
    }
  }
  else {
    cout << "c";
    flush(cout);
    cachedTests++;
  }

  if (cursor->data == VR_PASSED) {
    return true;
  }
  else {
    xassert(cursor->data == VR_FAILED);

    // 'n' seems to be relevant
    n->rel = R_RELEVANT;

    return false;
  }
}


VariantCursor Minimizer::write(int &size)
{
  VariantCursor cursor = results.getTop();
  size = tree->write(sourceFname, source, cursor);
  return cursor;
}


void Minimizer::minimize()
{
  if (!tree->getTop()) {
    return;
  }

  while (minimize(tree->getTop())) {
    // keep going as long as progress is being made
  }
}


bool Minimizer::minimize(Node *n)
{
  if (!n) {
    // nothing to do
    return false;
  }

  if (n->rel == R_IRRELEVANT_SIBS) {
    // this node and siblings are already known to be irrelevant
    return false;
  }

  if (n->rel == R_IRRELEVANT) {
    // the node itself is irrelevant, but siblings are still in play
    bool ret = false;
    ret = minimize(n->right) || ret;
    ret = minimize(n->left) || ret;
    return ret;
  }

  Relevance origRel = n->rel;

  // see if we can drop this node and its siblings
  int size;
  if (outerRunTest(size, n, R_IRRELEVANT_SIBS)) {
    // we have made progress
    cout << "\nred2: " << stringf("%10d", size) << " ";
    flush(cout);
    return true;
  }

  // for performance testing, would disable large-sections-first optimization
  //origRel = R_RELEVANT;

  if (origRel == R_UNKNOWN) {
    // this is the first time this node has been tested, so do not
    // test its children yet; instead wait for the next pass
    //
    // return 'true' to mean that we made progress in the sense of
    // turning this node's 'rel' from R_UNKNOWN to R_RELEVANT, and
    // consequently on the next pass we will investigate the
    // children
    return true;
  }

  // this node was tested at least once before, so now try dropping
  // some of its children
  xassert(origRel == R_RELEVANT);

  // try children from right to left; here we are testing both
  // siblings and subintervals, so as to leverage the existing tree
  bool ret = false;
  ret = minimize(n->right) || ret;

  // try dropping my entire range, including the spaces outside
  // any subintervals
  if (outerRunTest(size, n, R_IRRELEVANT)) {
    // we have made progress
    cout << "\nred1: " << stringf("%10d", size) << " ";
    flush(cout);
    ret = true;
  }
  else {
    // consider dropping subintervals
    ret = minimize(n->subintervals) || ret;
  }

  ret = minimize(n->left) || ret;

  return ret;
}


bool Minimizer::minimizeChildren(Node *sub)
{
  xfailure("not used right now");

  bool ret = false;

  // try minimizing later children first, with the idea that the
  // static semantic dependencies are likely to go from later to
  // earlier, hence we'd like to start dropping things at the
  // end of the file first
  if (sub->right) {
    ret = minimizeChildren(sub->right) || ret;
  }

  // now try minimizing this child
  ret = minimize(sub) || ret;

  // and earlier children
  if (sub->left) {
    ret = minimizeChildren(sub->left) || ret;
  }
  
  return ret;
}


void entry(int argc, char *argv[])
{
  xBase::logExceptions = false;
  string progName = argv[0];
  
  TRACE_ARGS();

  bool checktree = tracingSys("checktree");

  if (checktree) {
    if (argc != 3) {
      cout << "usage: " << progName << " [options] foo.c foo.c.str\n";
      return;
    }
  }
  else {
    if (argc != 4) {
      cout << "usage: " << progName << " [options] foo.c foo.c.str ./test-program\n";
      return;
    }
  }

  Minimizer m;
  m.sourceFname = argv[1];
  string backupFname = stringc << m.sourceFname << ".bak";
  string treeFname = argv[2];
  if (!checktree) {
    m.testProg = argv[3];
  }

  // back up the input
  if (!checktree &&
      0!=system(stringc << "cp \'" << m.sourceFname << "\' \'"
                        << backupFname << "\'")) {
    xfatal("failed to create " << backupFname);
  }

  // read the file into memory
  readFile(m.sourceFname, m.source);

  // build the interval partition tree
  cout << "building interval partition tree\n";
  m.tree = parseFile(treeFname);

  // check that its size does not exceed the source file
  {
    int endpt = m.tree->getLargestFiniteEndpoint();
    if (endpt >= m.source.size()) {
      xfatal("the interval tree ends at " << endpt <<
             ", but the file size is only " << m.source.size());
    }
  }

  if (checktree) {
    cout << "tree seems ok\n";
    return;     // done
  }

  // generate the original input
  int size;
  VariantCursor cursor = m.write(size);
  cout << "orig: " << stringf("%10d", size) << " ";
  flush(cout);

  // confirm it is the same as the given original
  if (0!=system(stringc << "cmp -s \'" << m.sourceFname << "\' \'"
                        << backupFname << "\'")) {
    xfatal("failed to accurately re-create original source file");
  }

  try {
    // confirm it passes the test
    m.testInputSum += size;
    cursor->data = m.runTest();
    if (cursor->data == VR_PASSED) {
      // yes
    }
    else {
      // no
      xfatal("original source file does not pass the test");
    }
  }
  catch (XCtrlC &) {
    HANDLER();
    xfatal("exiting due to ctrl-c; input file is unchanged");
  }

  // begin trying lots of variants
  try {
    m.minimize();

    cout << "\ndone!  writing minimized version to " << m.sourceFname << "\n";
  }
  catch (XCtrlC &) {
    HANDLER();
    cout << "\nuser pressed ctrl-c;\n";
    cout << m.sourceFname << " will be left as the smallest variant that passed the test\n";
  }

  // write the final minimized version
  cursor = m.write(size);
  xassert(cursor->data == VR_PASSED);

  cout << "passing=" << m.passingTests
       << ", failing=" << m.failingTests
       << ", total=" << (m.passingTests+m.failingTests)
       << ", inputSum=" << m.testInputSum
       << " (cached=" << m.cachedTests << ")"
       << "\n";

  // debugging stuff (interesting, but noisy)
  if (tracingSys("dumpfinal")) {
    m.tree->gdb();
    printResults(m.results);
  }
}

ARGS_MAIN
