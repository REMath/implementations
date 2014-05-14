// tobjpool.cc            see license.txt for copyright and terms of use
// test ObjectPool

#include "objpool.h"     // ObjectPool

#include <stdlib.h>      // rand


// class we're going to make a pool of
class Foo {
public:
  union {
    Foo *nextInFreeList;    // for ObjectPool
    int x;
  };
  int y;
  int z;

public:
  void establishInvariant(int index);
  void checkInvariant(int index) const;
  void deinit() {}
};

void Foo::establishInvariant(int index)
{
  x = index;
  y = x+1;
  z = y+1;
}

void Foo::checkInvariant(int index) const
{
  xassert(x == index);
  xassert(y == x+1);
  xassert(z == y+1);
}
                             

enum { SMALL=30, BIG=100, ITERS=10000 };

int main()
{
  ObjectPool<Foo> pool(SMALL);
  int i;    
  int numAllocated=0;

  // keep track of what I've allocated
  Foo **allocated = new Foo*[BIG];
  for (i=0; i<BIG; i++) {
    allocated[i] = NULL;
  }

  // start allocating at random
  cout << "allocating/deallocating " << ITERS << " times..\n";
  for (i=0; i<ITERS; i++) {
    int index = rand()%BIG;
    Foo *&f = allocated[index];

    if (f) {
      // deallocate
      f->checkInvariant(index);
      pool.dealloc(f);
      f = NULL;
      numAllocated--;
    }
    else {
      // allocate
      f = pool.alloc();
      f->establishInvariant(index);
      numAllocated++;
    }
  }

  // query pool size before cleaning up
  int startSize = pool.freeObjectsInPool();
  int finalNumAllocd = numAllocated;

  // deallocate all that remain
  cout << "freeing remaining " << numAllocated << " stragglers\n";
  for (i=0; i<BIG; i++) {
    if (allocated[i]) {
      Foo *&f = allocated[i];
      f->checkInvariant(i);
      pool.dealloc(f);
      f = NULL;
      numAllocated--;
    }
  }
  xassert(numAllocated==0);

  // verify that the # of objects freed is the # that became available
  xassert(finalNumAllocd == (pool.freeObjectsInPool() - startSize));

  cout << "pool capacity at end: " << pool.freeObjectsInPool() << endl;
  cout << "tobjpool works!\n";

  return 0;
}

