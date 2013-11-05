// bitarray.cc            see license.txt for copyright and terms of use
// code for bitarray.h

#include "bitarray.h"     // this module
#include "flatten.h"      // Flatten

#include <string.h>       // memset


BitArray::BitArray(int n)
  : numBits(n)
{
  allocBits();
  clearAll();
}

void BitArray::allocBits()
{
  bits = new unsigned char[allocdBytes()];
}


BitArray::~BitArray()
{
  delete[] bits;
}


BitArray::BitArray(Flatten&)
  : bits(NULL)
{}

void BitArray::xfer(Flatten &flat)
{
  flat.xferInt(numBits);

  if (flat.reading()) {
    allocBits();
  }
  flat.xferSimple(bits, allocdBytes());
}


BitArray::BitArray(BitArray const &obj)
  : numBits(obj.numBits)
{
  allocBits();
  memcpy(bits, obj.bits, allocdBytes());
}

void BitArray::operator=(BitArray const &obj)
{
  if (numBits != obj.numBits) {
    delete[] bits;
    numBits = obj.numBits;
    allocBits();
  }
  memcpy(bits, obj.bits, allocdBytes());
}


bool BitArray::operator== (BitArray const &obj) const
{
  if (numBits != obj.numBits) {
    return false;
  }
  
  // this relies on the invariant that the unused trailing
  // bits are always set to 0
  return 0==memcmp(bits, obj.bits, allocdBytes());
}


void BitArray::clearAll()
{
  memset(bits, 0, allocdBytes());
}


void BitArray::invert()
{
  int allocd = allocdBytes();
  for (int i=0; i<allocd; i++) {
    bits[i] = ~(bits[i]);
  }

  if (numBits & 7) {
    // there are some trailing bits that I need to flip back
    unsigned char mask = (1 << (numBits & 7)) - 1;     // bits to *not* flip
    bits[allocd-1] ^= ~mask;
  }
}


void BitArray::selfCheck() const
{
  if (numBits & 7) {
    // there are some trailing bits that I need to check
    unsigned char mask = (1 << (numBits & 7)) - 1;     // bits to *not* check
    unsigned char zero = bits[allocdBytes()-1] & ~mask;
    xassert(zero == 0);
  }
}


void BitArray::unionWith(BitArray const &obj)
{
  xassert(numBits == obj.numBits);

  int allocd = allocdBytes();
  for (int i=0; i<allocd; i++) {
    bits[i] |= obj.bits[i];
  }
}


void BitArray::intersectWith(BitArray const &obj)
{
  xassert(numBits == obj.numBits);

  int allocd = allocdBytes();
  for (int i=0; i<allocd; i++) {
    bits[i] &= obj.bits[i];
  }
}


// it's a little strange to export this function, since it is not
// very general-purpose, but that is the price of encapsulation
bool BitArray::anyEvenOddBitPair() const
{
  int allocd = allocdBytes();
  for (int i=0; i<allocd; i++) {
    unsigned char b = bits[i];
    if (b & (b >> 1) & 0x55) {        // 01010101
      return true;
    }
  }
  
  return false;    // no such pair
}


BitArray stringToBitArray(char const *src)
{
  int len = strlen(src);
  BitArray ret(len);
  for (int i=0; i<len; i++) {
    if (src[i]=='1') {
      ret.set(i);
    }
  }
  return ret;
}

string toString(BitArray const &b)
{
  int len = b.length();
  stringBuilder ret(len);
  for (int i=0; i<len; i++) {
    ret[i] = b.test(i)? '1' : '0';
  }
  return ret;
}


// ----------------------- BitArray::Iter ------------------------
void BitArray::Iter::adv()
{
  curBit++;

  while (curBit < arr.numBits) {
    if ((curBit & 7) == 0) {
      // beginning a new byte; is it entirely empty?
      while (arr.bits[curBit >> 3] == 0) {
        // yes, skip to next
        curBit += 8;

        if (curBit >= arr.numBits) {
          return;     // done iterating
        }
      }
    }

    // this could be made a little faster by using the trick to scan
    // for the first nonzero bit.. but since I am only going to scan
    // within a single byte, it shouldn't make that much difference
    if (arr.test(curBit)) {
      return;         // found element
    }

    curBit++;
  }
}


// -------------------- test code -------------------
#ifdef TEST_BITARRAY

#include "test.h"     // USUAL_MAIN

string toStringViaIter(BitArray const &b)
{ 
  stringBuilder sb;
  int index = 0;

  for (BitArray::Iter iter(b); !iter.isDone(); iter.adv()) {
    while (index < iter.data()) {
      sb << "0";
      index++;
    }
    sb << "1";
    index++;
  }
  
  while (index < b.length()) {
    sb << "0";
    index++;
  }
  
  return sb;
}


void testIter(char const *str)
{                             
  BitArray b = stringToBitArray(str);
  b.selfCheck();

  string s1 = toString(b);
  string s2 = toStringViaIter(b);
  if (s1 != s2 ||
      !s1.equals(str)) {
    cout << "str: " << str << endl;
    cout << " s1: " << s1 << endl;
    cout << " s2: " << s2 << endl;
    xbase("testIter failed");
  }

  // also test the inverter
  BitArray c = ~b;
  c.selfCheck();
  
  stringBuilder inv;                 
  int len = strlen(str);
  for (int i=0; i<len; i++) {
    inv << (str[i]=='0'? '1' : '0');
  }

  string cStr = toString(c);
  if (!inv.equals(cStr)) {
    cout << " inv: " << inv << endl;
    cout << "cStr: " << cStr << endl;
    xbase("test inverter failed");
  }
}


void testUnionIntersection(char const *s1, char const *s2)
{
  int len = strlen(s1);
  xassert(len == (int)strlen(s2));

  BitArray b1 = stringToBitArray(s1);
  BitArray b2 = stringToBitArray(s2);

  stringBuilder expectUnion, expectIntersection;
  for (int i=0; i<len; i++) {
    expectUnion        << ((s1[i]=='1' || s2[i]=='1')? '1' : '0');
    expectIntersection << ((s1[i]=='1' && s2[i]=='1')? '1' : '0');
  }
  
  BitArray u = b1 | b2;
  BitArray i = b1 & b2;
  
  string uStr = toString(u);
  string iStr = toString(i);

  if (!uStr.equals(expectUnion)) {
    cout << "         s1: " << s1 << endl;
    cout << "         s2: " << s2 << endl;
    cout << "       uStr: " << uStr << endl;
    cout << "expectUnion: " << expectUnion << endl;
    xbase("test union failed");
  }

  if (!iStr.equals(expectIntersection)) {
    cout << "                s1: " << s1 << endl;
    cout << "                s2: " << s2 << endl;
    cout << "              iStr: " << iStr << endl;
    cout << "expectIntersection: " << expectIntersection << endl;
    xbase("test intersection failed");
  }
}


void testAnyEvenOddBitPair(char const *s, bool expect)
{
  BitArray b = stringToBitArray(s);
  bool answer = b.anyEvenOddBitPair();
  if (answer != expect) {
    static char const *boolName[] = { "false", "true" };
    cout << "     s: " << s << endl;
    cout << "answer: " << boolName[answer] << endl;
    cout << "expect: " << boolName[expect] << endl;
    xbase("test anyEvenOddBitPair failed");
  }
}


void entry()
{
        //            1111111111222222222233333333334444444444555555555566
        //  01234567890123456789012345678901234567890123456789012345678901
  testIter("00000000111111111111000000000000");
  testIter("00000000000000000000000000000000000000111111111111000000000000");
  testIter("000000000000000000000000000000000000000111111111111000000000000");
  testIter("0000000000000000000000000000000000000000111111111111000000000000");
  testIter("00000000000000000000000000000000000000000111111111111000000000000");
  testIter("000000000000000000000000000000000000000000111111111111000000000000");
  testIter("0000000000000000000000000000000000000000000111111111111000000000000");
  testIter("00000000000000000000000000000000000000000000111111111111000000000000");
  testIter("000000000000000000000000000000000000000000000111111111111000000000000");
  testIter("0000000000000000000000000000000000000000000000111111111111000000000000");
  testIter("00000000000000000000000000000000000000000000000111111111111000000000000");
  testIter("000000000000000000000000000000000000000000000000111111111111000000000000");

  testIter("0101");
  testIter("1");
  testIter("0");
  testIter("");
  testIter("1111");
  testIter("0000");
  testIter("000000000000111111111111000000000000");
  testIter("111111111111111000000000000011111111");
  testIter("10010110010101010100101010101010100110001000100001010101111");

  testUnionIntersection("", 
                        "");

  testUnionIntersection("1",
                        "0");

  testUnionIntersection("10",
                        "00");

  testUnionIntersection("1001000100111110101001001001011111",
                        "0001100101011101011010000111010110");

  testUnionIntersection("1111111111111111111111111111111111",
                        "0000000000000000000000000000000000");

  testUnionIntersection("0000111111000001111110000011110000",
                        "1111000000111110000001111100001111");
            
  testAnyEvenOddBitPair("0000", false);
  testAnyEvenOddBitPair("0001", false);
  testAnyEvenOddBitPair("0010", false);
  testAnyEvenOddBitPair("0100", false);
  testAnyEvenOddBitPair("1000", false);
  testAnyEvenOddBitPair("0110", false);
  testAnyEvenOddBitPair("1110", true);
  testAnyEvenOddBitPair("0111", true);
  testAnyEvenOddBitPair("1111", true);
  testAnyEvenOddBitPair("11110", true);
  testAnyEvenOddBitPair("01100", false);

  cout << "bitarray is ok\n";
}

USUAL_MAIN

#endif // TEST_BITARRAY
