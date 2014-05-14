// iptree.cc
// code for iptree.h

#include "iptree.h"       // this module
#include "autofile.h"     // AutoFILE
#include "syserr.h"       // xsyserror
#include "trace.h"        // TRACE


// --------------------- Relevance ----------------------
char const *toString(Relevance r)
{
  char const * const map[] = {
    "R_IRRELEVANT_SIBS",
    "R_IRRELEVANT",
    "R_UNKNOWN",
    "R_RELEVANT"
  };

  STATIC_ASSERT(TABLESIZE(map) == NUM_RELEVANCES);
  xassert((unsigned)r < (unsigned)NUM_RELEVANCES);
  return map[r];
}


// ------------------- VariantResults -------------------
char const *toString(VariantResult r)
{
  char const * const map[] = {
    "VR_UNKNOWN",
    "VR_PASSED",
    "VR_FAILED"
  };

  STATIC_ASSERT(TABLESIZE(map) == NUM_VRESULTS);
  xassert((unsigned)r < (unsigned)NUM_VRESULTS);
  return map[r];
}


void printBits(ArrayStack<char> const &bits)
{
  for (int i=0; i < bits.length(); i++) {
    cout << (bits[i]? '1' : '0');
  }
}


void iprintResults(VariantCursor p, ArrayStack<char> &bits)
{
  if (p->data) {
    // print the result
    cout << toString(p->data) << "  ";

    // and the bitstring
    printBits(bits);
    cout << "\n";
  }

  if (p->zero) {
    bits.push(0);
    iprintResults(p->zero, bits);
    bits.pop();
  }

  if (p->one) {
    bits.push(1);
    iprintResults(p->one, bits);
    bits.pop();
  }
}


void printResults(VariantResults &results)
{
  ArrayStack<char> bits;
  VariantCursor p = results.getTop();

  iprintResults(p, bits);
}


// ---------------------- Interval ----------------------
string Interval::rangeString() const
{
  if (hi < INT_MAX) {
    return stringc << "[" << lo << ", " << hi << "]";
  }
  else {
    return stringc << "[" << lo << ", +inf)";
  }
}


// ------------------------ Node ------------------------
long Node::linkChases = 0;

Node::Node(int lo, int hi)
  : ival(lo, hi),
    left(NULL),
    right(NULL),
    subintervals(NULL),
    rel(R_UNKNOWN)
{
  xassert(lo <= hi);
}

Node::~Node()
{
  if (left) {
    delete left;
  }
  if (right) {
    delete right;
  }
  if (subintervals) {
    delete subintervals;
  }
}


bool Node::contains(Node const *n) const
{
  return ival.contains(n->ival);
}


bool Node::contains(int n) const
{
  return ival.contains(n);
}


int Node::getLeftEdge() const
{
  if (left) {
    return left->getLeftEdge();
  }
  else {
    return ival.lo;
  }
}

int Node::getRightEdge() const
{
  if (right) {
    return right->getRightEdge();
  }
  else {
    return ival.hi;
  }
}


void Node::insert(Node *n)
{
  if (n->ival < this->ival) {
    // goes into left subtree
    if (!left) {
      left = n;
    }
    else {
      linkChases++;
      left->insert(n);
    }
    return;
  }

  if (n->ival > this->ival) {
    // goes into right subtree
    if (!right) {
      right = n;
    }
    else {
      linkChases++;
      right->insert(n);
    }
    return;
  }

  if (this->contains(n)) {
    // goes into subintervals
    if (!subintervals) {
      subintervals = n;
    }
    else {
      subintervals->insert(n);
    }
    return;
  }

  xfatal("improper overlap: " << n->rangeString() <<
         " and " << this->rangeString());
}


Node const *Node::queryC(int n) const
{
  xassert(contains(n));

  // search among subintervals for containing node
  Node const *sub = subintervals;
  while (sub) {
    if (sub->ival.contains(n)) {
      return sub->queryC(n);
    }
    
    if (n < sub->ival) {
      sub = sub->left;
    }
    else {
      xassert(n > sub->ival);
      sub = sub->right;
    }
  }

  // no subinterval contains it
  return this;
}


int writeSegment(FILE *fp, GrowArray<char> const &source,
                 int start, int len)
{
  xassert(len >= 0);
  xassert(start >= 0);
  xassert(start+len <= source.size());

  fwrite(source.getArray()+start, 1, len, fp);
  
  return len;
}




// The following diagram depicts the situation when a node ("me") is
// asked to print itself.  It is responsible for printing everything
// from A (the left edge of the left sibling tree) to H (the right
// edge of the right sibling tree).
//                                                               .
//                               me                              .
//                        +---------------+                      .
//                        |               |                      .
//          left          |               |        right         .
//        +--------+      |      sub      |     +---------+      .
//        |        |      |     +--+      |     |         |      .
//        |        |      |     |  |      |     |         |      .
//       /|        |\     |    /|  |\     |    /|         |\     .
//      / |        | \    |   / |  | \    |   / |         | \    .
//      A            B    C   D      E    F   G             H    .
//
// This requires several steps:
//   - A-B: ask 'left' to print itself
//   - B-D: I do this
//   - D-E: ask 'subintervals' to print itself
//   - E-G: I do this
//   - G-H: ask 'right' to print itself
//
// If 'rel' is R_IRRELEVANT_SIBS, print nothing.
//
// If 'left' is NULL, then A=B=C.
// If 'right' is NULL, then F=G=H.
//
// If 'rel' is R_IRRELEVANT, omit C-F.
//
// If 'subintervals' is null, then I just print B-G.
int Node::write(FILE *fp, GrowArray<char> const &source,
                VariantCursor &cursor) const
{
  if (rel == R_IRRELEVANT_SIBS) {
    // my entire range, from A to H, is cancelled
    cursor = cursor->getZero();
    return 0;
  }
  cursor = cursor->getOne();

  // # of bytes printed so far
  int ret = 0;

  int B;
  if (left) {
    ret += left->write(fp, source, cursor);          // print A-B
    B = left->getRightEdge();
  }
  else {
    // so when I print B-D, I will actually print C-D
    B = ival.lo-1;
  }

  int E;
  if (rel > R_IRRELEVANT) {
    cursor = cursor->getOne();
    if (subintervals) {
      int D = subintervals->getLeftEdge();
      ret += writeSegment(fp, source, B+1, D-(B+1));   // print B-D
      ret += subintervals->write(fp, source, cursor);  // print D-E
      E = subintervals->getRightEdge();
    }
    else {
      // so when I print E-G, I will actually print B-G
      E = B;
    }
  }
  else {
    cursor = cursor->getZero();

    // omit C-F
    int C = ival.lo;
    ret += writeSegment(fp, source, B+1, C-(B+1));   // print B-C
    
    // so when I print E-G, I will actually print F-G
    E = ival.hi;
  }

  int G;
  if (right) {
    G = right->getLeftEdge();
    ret += writeSegment(fp, source, E+1, G-(E+1));   // print E-G
    ret += right->write(fp, source, cursor);         // print G-H
  }
  else {
    G = ival.hi+1;
    ret += writeSegment(fp, source, E+1, G-(E+1));   // print E-G
  }
  
  return ret;
}


// recursively explore the sibling tree
int Node::writeSubs(FILE *fp, GrowArray<char> const &source,
                    VariantCursor &cursor, int &curOffset)
{
  xfailure("not used anymore");

  // write left siblings
  int ret = 0;
  if (left) {
    ret += left->writeSubs(fp, source, cursor, curOffset);
  }

  // write data preceding me
  ret += writeSegment(fp, source, curOffset, ival.lo - curOffset);

  // possibly write me
  if (rel > R_IRRELEVANT) {
    cursor = cursor->getOne();
    ret += write(fp, source, cursor);
  }
  else {
    cursor = cursor->getZero();
  }
  curOffset = ival.hi+1;

  // write right siblings
  if (right) {
    ret += right->writeSubs(fp, source, cursor, curOffset);
  }
  
  return ret;
}


static void indent(ostream &os, int ind)
{
  for (int i=0; i<ind; i++) {
    os << ' ';
  }
}

void Node::debugPrint(ostream &os, int ind) const
{
  indent(os, ind);
  cout << rangeString() << " \t" << toString(rel) << "\n";

  if (subintervals) {
    subintervals->debugPrintSubs(os, ind+2);
  }
}

void Node::debugPrintSubs(ostream &os, int ind) const
{
  // left siblings
  if (left) {
    left->debugPrintSubs(os, ind);
  }
            
  // myself
  debugPrint(os, ind);
  
  // right siblings
  if (right) {
    right->debugPrintSubs(os, ind);
  }
}


// ------------------------ IPTree -----------------------
IPTree::IPTree(int hi)
  : top(NULL)
{
  top = new Node(0, hi);
}

IPTree::~IPTree()
{
  delete top;
}


Node *IPTree::insert(int lo, int hi)
{ 
  Node *n = new Node(lo, hi);
  top->insert(n);
  return n;
}


Node const *IPTree::queryC(int n) const
{
  if (!top || !top->contains(n)) {
    return NULL;
  }

  return top->queryC(n);
}


int IPTree::write(rostring fname, GrowArray<char> const &source,
                  VariantCursor &cursor) const
{
  AutoFILE fp(toCStr(fname), "w");
  int ret = 0;

  if (top->rel) {
    cursor = cursor->getOne();
    ret += top->write(fp, source, cursor);
  }
  else {
    cursor = cursor->getZero();
  }

  return ret;
}


int IPTree::getLargestFiniteEndpoint()
{
  if (top->ival.hi < INT_MAX) {
    return top->ival.hi;
  }

  Node *sub = top->subintervals;
  if (!sub) {
    return top->ival.lo;
  }
  
  while (sub->right) {
    sub = sub->right;
  }

  return sub->ival.hi;
}


void IPTree::gdb() const
{
  if (!top) {
    cout << "(empty tree)\n";
  }
  else {
    top->debugPrint(cout, 0);
  }
}


// ---------------------- readFile -----------------------
void readFile(rostring fname, GrowArray<char> &dest)
{
  AutoFILE fp(toCStr(fname), "r");

  enum { SZ=4096 };
  int curOffset = 0;

  for (;;) {
    dest.ensureIndexDoubler(curOffset+SZ);
    int len = fread(dest.getArrayNC()+curOffset, 1, SZ, fp);
    if (len < 0) {
      xsyserror("read");
    }
    if (len == 0) {
      break;
    }

    curOffset += len;
  }
  
  // trim the array
  dest.setSize(curOffset);
}


// ---------------------- test code ----------------------
#ifdef TEST_IPTREE
#include "test.h"        // USUAL_MAIN

void entry()
{
  IPTree t(115);         // whole file

  t.insert(0,9);         // prelude
  t.insert(10,16);       // int g;
  t.insert(17,23);       // int h;
  t.insert(24,41);       // int bar(int,int);
  t.insert(42,42);       // whitespace

  t.insert(43,113);      // all of foo
  t.insert(51,62);       // parameter list
  t.insert(56,62);       // ", int y"

  t.insert(69,75);       // "g += x;"
  t.insert(71,74);       // "+= x"
  t.insert(71,71);       // "+"

  t.insert(79,92);       // "h = g + x + y";
  t.insert(81,91);       // "= g + x + y"
  t.insert(85,87);       // "+ x"
  t.insert(89,91);       // "+ y"

  t.insert(96,111);      // "return bar(2,3);"
  t.insert(103,110);     // "bar(2,3)"
  t.insert(107,109);     // "2,3"
  t.insert(108,109);     // ",3"

  t.gdb();
}

USUAL_MAIN

#endif // TEST_IPTREE

