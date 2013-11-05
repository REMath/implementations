// bitstrmap.h
// map from finite bitstrings to some object

// This is not a BDD because:
//   - I want to map to arbitrary objects, not just 0 or 1.
//   - I do not expect much useful sharing.

#ifndef BITSTRMAP_H
#define BITSTRMAP_H

template <class T>
class BitStrMap {
public:      // types
  class Node {
  public:    // data
    // domain object, or 0 if not mapped
    T data;

    // child if next bit in string is 0, or NULL if there are
    // no mapped objects there (owner)
    Node *zero;

    // similar for 1
    Node *one;

  public:
    Node() : data((T)0), zero(NULL), one(NULL) {}
    ~Node();
    
    // get a successor, creating it if necessary
    Node *getZero();
    Node *getOne();
    Node *getSucc(bool which)
      { return which? getOne() : getZero(); }
  };

private:     // data
  // first node in tree, corresponding to empty bitstring
  // (nullable owner)
  Node *top;

public:      // funcs
  BitStrMap() : top(NULL) {}
  ~BitStrMap();
  
  // get or create
  Node *getTop();
};


// ------------------- Node implementation ----------------------
template <class T>
BitStrMap<T>::Node::~Node()
{
  if (zero) {
    delete zero;
  }
  if (one) {
    delete one;
  }
}


template <class T>
typename BitStrMap<T>::Node *BitStrMap<T>::Node::getZero()
{
  if (!zero) {
    zero = new Node;
  }
  return zero;
}


template <class T>
typename BitStrMap<T>::Node *BitStrMap<T>::Node::getOne()
{
  if (!one) {
    one = new Node;
  }
  return one;
}


// ------------------ BitStrMap implementation ------------------
template <class T>
BitStrMap<T>::~BitStrMap()
{
  if (top) {
    delete top;
  }
}


template <class T>
typename BitStrMap<T>::Node *BitStrMap<T>::getTop()
{
  if (!top) {
    top = new Node;
  }
  return top;
}


#endif // BITSTRMAP_H
