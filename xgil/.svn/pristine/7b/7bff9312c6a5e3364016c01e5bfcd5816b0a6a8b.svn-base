// testmalloc.cc            see license.txt for copyright and terms of use
// test malloc, test heap walk, etc.
  
#include <stdio.h>     // printf
#include <unistd.h>    // write
#include <string.h>    // strlen
#include <stdlib.h>    // malloc

#include "ckheap.h"    // malloc functions


HeapWalkOpts myWalker(void *block, int size)
{
  printf("  block at %p, size %d\n", block, size);
  return HW_GO;
}


void *toDealloc;
HeapWalkOpts deallocWalker(void *block, int size)
{
  if (block == toDealloc) {
    printf("deallocating block at %p, size %d\n", block, size);
    return HW_FREE;
  }
  return HW_GO;
}


#define MSGOUT(str) write(1, str, strlen(str))

void heapWalk(char const *context)
{
  printf("%s: heap contents:\n", context);
  walkMallocHeap(myWalker);
}

#define TRACERET(expr)                      \
  printf("%s returned %p\n", #expr, expr);  \
  heapWalk(#expr);                          \
  malloc_stats()

#define TRACE(expr)                         \
  expr;                                     \
  heapWalk(#expr);                          \
  malloc_stats()


void test1()
{
  printf("--------- test1 ---------\n");
  
  void *p1, *p2, *p3, *p4, *p5, *p6;

  heapWalk("start");

  TRACERET(p1 = malloc(5));
  TRACERET(p2 = malloc(70));
  TRACERET(p3 = malloc(1000));
  TRACERET(p4 = malloc(10000));
  TRACERET(p5 = malloc(100000));
  
  // this last size is potentially interesting because it's
  // beyond the 128k default threshold for when dlmalloc
  // uses mmap() instead of sbrk() to get memory from the OS
  TRACERET(p6 = malloc(1000000));

  toDealloc = p3;
  TRACE(walkMallocHeap(deallocWalker));

  TRACE(free(p1));
  TRACE(free(p5));
  //TRACE(free(p3));   // done by above
  TRACE(free(p6));
  TRACE(free(p2));
  TRACE(free(p4));
}


void test2()
{
  printf("--------- test2 ---------\n");

  void *arr[100];
  memset(arr, 0, sizeof(arr));

  for (int i=0; i < 10000; i++) {
    // pick a random slot
    int slot = random() % 100;

    if (arr[slot] == NULL) {
      // allocate something
      arr[slot] = malloc(random() % 1000);
    }

    else if (random()%4 != 0) {
      // dealloc directly
      free(arr[slot]);
      arr[slot] = NULL;
    }

    else {
      // dealloc by walk
      toDealloc = arr[slot];
      walkMallocHeap(deallocWalker);
      arr[slot] = NULL;
    }
  }

  // snapshot now
  heapWalk("snapshot after test2");  

  // free the rest
  for (int j=0; j<100; j++) {
    if (arr[j]) {
      free(arr[j]);
    }
  }
}


int main()
{
  test1();
  test2();

  MSGOUT("testmalloc finished\n");
  return 0;
}

