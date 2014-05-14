// ssxnode.h            see license.txt for copyright and terms of use
// parse tree node for SSx.tree.gr

#ifndef SSXNODE_H
#define SSXNODE_H
                      
// for storing counts of parse trees
typedef int TreeCount;

class Node {
public:
  enum Type { MERGE, SSX, X } type;
  Node *left, *right;
  TreeCount count;       // # of parse trees of which this is the root

public:
  Node(Type t, Node *L, Node *R)
    : type(t), left(L), right(R), count(0) {}
};

#endif // SSXNODE_H
