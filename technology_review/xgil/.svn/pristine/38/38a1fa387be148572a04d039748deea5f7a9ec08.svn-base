// iptree.h
// interval partition tree

#ifndef IPTREE_H
#define IPTREE_H

#include "objlist.h"        // ObjList
#include "str.h"            // rostring
#include "array.h"          // GrowArray
#include "bitstrmap.h"      // BitStrMap

#include <stdio.h>          // FILE
#include <limits.h>         // INT_MAX


// node relevance
enum Relevance {
  R_IRRELEVANT_SIBS,        // my siblings and I are all irrelevant
  R_IRRELEVANT,             // was irrelevant at least once
  R_UNKNOWN,                // never tested
  R_RELEVANT,               // has been relevant every time tested
  NUM_RELEVANCES
};

char const *toString(Relevance r);


// result of applying the test to a variant
enum VariantResult {
  VR_UNKNOWN=0,             // never tried
  VR_PASSED,                // test passed
  VR_FAILED,                // test failed
  NUM_VRESULTS
};

char const *toString(VariantResult r);


// map a variant bitstring to its result code
typedef BitStrMap<VariantResult> VariantResults;
typedef VariantResults::Node *VariantCursor;

// debugging: print the set of mapped bitvectors
void printResults(VariantResults &results);


class Interval {
public:      // data
  // interval endpoints, inclusive; hi can be INT_MAX
  int lo, hi;

public:      // funcs
  Interval() : lo(0), hi(0) {}
  Interval(int L, int H) : lo(L), hi(H) {}

  Interval& operator= (Interval const &obj)
    { lo=obj.lo; hi=obj.hi; return *this; }

  // number of elements in the interval
  int size() const
    { return hi-lo+1; }

  // interval comparison
  bool contains(Interval const &obj) const
    { return lo <= obj.lo && obj.hi <= hi; }
  bool operator< (Interval const &obj) const
    { return hi < obj.lo; }
  bool operator> (Interval const &obj) const
    { return lo > obj.hi; }

  // integer comparison
  bool contains(int n) const
    { return lo <= n && n <= hi; }
  bool operator< (int n) const
    { return hi < n; }
  bool operator> (int n) const
    { return lo > n; }
  friend bool operator< (int n, Interval const &obj)
    { return n < obj.lo; }
  friend bool operator> (int n, Interval const &obj)
    { return n > obj.hi; }

  // print the range as a string, like "[1, 2]"
  string rangeString() const;
};


// node in the interval tree
class Node {
public:
  // interval
  Interval ival;

  // binary search tree of siblings; this tree is not necessarily
  // balanced, but the tree construction procedure has provisions to
  // make balance reasonably likely (nullable owner)
  Node *left, *right;

  // subintervals contained within this one
  Node *subintervals;

  // state of search for minimal element
  Relevance rel;

  // # of times 'left' or 'right' is traversed during insert()
  static long linkChases;

private:     // funcs
  int writeSubs(FILE *fp, GrowArray<char> const &source,
                VariantCursor &cursor, int &curOffset);
  void debugPrintSubs(ostream &os, int ind) const;

public:      // funcs
  Node(int lo, int hi);
  ~Node();

  // true if 'this' contains or equals 'n'
  bool contains(Node const *n) const;

  // true if 'this' contains the value 'n'
  bool contains(int n) const;

  // follow 'left' to the end, and get 'lo' there
  int getLeftEdge() const;

  // follow 'right' to end and get 'hi'
  int getRightEdge() const;

  // add 'n' somewhere in the subtree rooted at 'this'
  void insert(Node *n);

  // find the smallest interval containing 'n', which must at least
  // be contained within 'this'
  Node const *queryC(int n) const;
  Node *query(int n) { return const_cast<Node*>(queryC(n)); }

  // write this node's fragment from 'source' to 'fp', returning
  // the # of bytes written
  int write(FILE *fp, GrowArray<char> const &source,
            VariantCursor &cursor) const;

  // print the range as a string, like "[1, 2]"
  string rangeString() const
    { return ival.rangeString(); }

  // print this subtree to the given stream at the given level
  // of indentation
  void debugPrint(ostream &os, int ind) const;
};


// interval partition tree
class IPTree {
private:     // data
  // (owner) top of the tree
  Node *top;

public:      // funcs
  IPTree(int hi);      // hi is 'hi' of root
  ~IPTree();

  Node *getTop() { return top; }

  // add a new interval; must nest properly *inside* existing
  // intervals (so must insert from largest to smallest)
  Node *insert(int lo, int hi);

  // find the smallest interval containing the given value, or NULL if
  // it is outside all intervals
  Node const *queryC(int n) const;
  Node *query(int n) { return const_cast<Node*>(queryC(n)); }

  // given an array of source characters, write to 'fname' a file
  // consisting of all the intervals that are not irrelevant; the
  // cursor is advanced to reflect the navigation path; return the
  // # of bytes written
  int write(rostring fname, GrowArray<char> const &source,
            VariantCursor &cursor) const;
                                 
  // what is the largest endpoint, other than INT_MAX?
  int getLargestFiniteEndpoint();

  // debugging: print the tree to stdout
  void gdb() const;
};


// read a file into memory
void readFile(rostring fname, GrowArray<char> &dest);


#endif // IPTREE_H
