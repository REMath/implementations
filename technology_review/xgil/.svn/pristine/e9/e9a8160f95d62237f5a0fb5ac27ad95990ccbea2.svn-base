// bitarray.h            see license.txt for copyright and terms of use
// one-dimensional array of bits

#ifndef BITARRAY_H
#define BITARRAY_H

#include "xassert.h"      // xassert
#include "str.h"          // string

class Flatten;            // flatten.h

class BitArray {
private:    // data
  unsigned char *bits;
  int numBits;              // # of bits in the array
  
  // invariant: the bits in the last allocated byte that are beyond
  // 'numBits' (if any) are always 0

private:    // funcs
  void bc(int i) const { xassert((unsigned)i < (unsigned)numBits); }
  int allocdBytes() const { return (numBits+7) / 8; }
  void allocBits();

public:     // funcs
  BitArray(int n);          // create with given # of bits, initially zeroed
  ~BitArray();

  BitArray(Flatten&);
  void xfer(Flatten &flat);

  BitArray(BitArray const &obj);
  void operator=(BitArray const &obj);

  bool operator== (BitArray const &obj) const;
  bool operator!= (BitArray const &obj) const { return !operator==(obj); }

  int length() const
    { return numBits; }

  // test a bit, return 0 or 1
  int test(int i) const
    { bc(i); return ((bits[i >> 3]) >> (i & 7)) & 1; }

  // set a bit to a specific value
  void set(int i)
    { bc(i); bits[i >> 3] |= (1 << (i & 7)); }
  void reset(int i)
    { bc(i); bits[i >> 3] &= ~(1 << (i & 7)); }

  // set a bit to an arbitrary value
  void setTo(int i, int val) {
    if (val) {
      set(i);
    }
    else {
      reset(i);
    }
  }

  // clear all bits
  void clearAll();
  
  // invert the bits
  void invert();

  // bitwise OR ('obj' must be same length)
  void unionWith(BitArray const &obj);
  
  // bitwise AND
  void intersectWith(BitArray const &obj);
                                 
  // true if there is any pair of bits 2n,2n+1 where both are set
  bool anyEvenOddBitPair() const;

  // debug check
  void selfCheck() const;

  // operators
  BitArray operator~ () const {
    BitArray ret(*this);
    ret.invert();
    return ret;
  }

  BitArray& operator|= (BitArray const &obj) {
    unionWith(obj);
    return *this;
  }

  BitArray operator| (BitArray const &obj) const {
    BitArray ret(*this);
    ret.unionWith(obj);
    return ret;
  }

  BitArray& operator&= (BitArray const &obj) {
    intersectWith(obj);
    return *this;
  }

  BitArray operator& (BitArray const &obj) const {
    BitArray ret(*this);
    ret.intersectWith(obj);
    return ret;
  }

public:     // types
  class Iter {
  private:    // data
    BitArray const &arr;    // array we are reading
    int curBit;             // bit at 'data'; is >= 'numBits' when done

  public:     // funcs
    Iter(BitArray const &a)
      : arr(a), curBit(-1) { adv(); }

    bool isDone() const   { return curBit >= arr.numBits; }
    int data() const      { return curBit; }

    void adv();
  };
  friend class Iter;
};


BitArray stringToBitArray(char const *src);
string toString(BitArray const &b);


#endif // BITARRAY_H
