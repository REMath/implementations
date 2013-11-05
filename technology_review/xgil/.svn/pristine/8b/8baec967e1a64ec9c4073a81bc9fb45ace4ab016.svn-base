// smin.h
// structural minimizer

#ifndef SMIN_H
#define SMIN_H

#include "iptparse.h"       // parseFile
#include "iptree.h"         // IPTree
#include "exc.h"            // xBase


// thrown when Ctrl-C pressed
class XCtrlC : public xBase {
public:
  XCtrlC();
  XCtrlC(XCtrlC const &obj);
  ~XCtrlC();
};



class Minimizer {
public:      // data
  // filenames
  string sourceFname;       // source file to minimize
  string testProg;          // test program to run

  // original contents of 'sourceFname;
  GrowArray<char> source;
  
  // structural info about 'source'; must be set by client 
  // (nullable owner)
  IPTree *tree;
  
  // record of which variants have been tried
  VariantResults results;
  
  // count of tests run
  int passingTests;
  int failingTests;
  int cachedTests;
  
  // sum of the lengths of all inputs tested
  long long testInputSum;

private:     // funcs    
  bool minimize(Node *n);
  bool minimizeChildren(Node *sub);

public:      // funcs
  Minimizer();
  ~Minimizer();

  // run the test with the current contents of the source file
  VariantResult runTest();

  // write the variant corresponding to the current state of the tree
  // nodes' relevance, and return a cursor denoting the bitstring for
  // this variant; returns with 'size' set to size of written file
  VariantCursor write(int &size);

  // possibly use the cache; consider setting n->rel to 'ret';
  // return true if the current variant passes
  bool outerRunTest(int &size, Node *n, Relevance rel);

  // kick off the minimizer
  void minimize();
};

#endif // SMIN_H
