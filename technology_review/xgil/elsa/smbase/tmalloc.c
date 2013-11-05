// tmalloc.c            see license.txt for copyright and terms of use
// test malloc implementation in DEBUG_HEAP configuration

#include <stdlib.h>     // malloc
#include <stdio.h>      // printf

#include "mysig.h"      // setHandler
#include "ckheap.h"     // checkHeap
                

typedef void (*Fn)(void);


void expectFail(Fn f)
{
  if (setjmp(sane_state) == 0) {
    setHandler(SIGABRT, jmpHandler);
    setHandler(SIGSEGV, jmpHandler);
    f();
    printf("should have caught that\n");
    exit(2);
  }
  else {
    printf("caught error ok\n");
  }
}


void offEnd()
{
  char *p = malloc(10);
  p[10] = 7;    // oops
  free(p);
}

void offEndCheck()
{
  char *p = malloc(10);
  p[10] = 7;    // oops
  
  // instead of using free() to find the error,
  // find it with checkHeap
  checkHeap();
}

void offBeg()
{
  char *p = malloc(15);
  p[-2] = 8;
  free(p);
}

void ok()
{
  char *p = malloc(20);
  p[0] = 5;
  p[19] = 9;
  free(p);
}

void dangle()
{
  char **p = malloc(20);
  *p = (char*)(p+4);    // *p is a pointer to 4 bytes later
  **p = 8;              // should work ok
  free(p);
  **p = 7;              // should hit the 0xBB trap
}

void doubleFree()
{
  char *p = malloc(10);
  free(p);
  free(p);
}

int main()
{   
  // do some benign things
  int i;
  for (i=0; i<10; i++) {
    int size = rand() % 100;
    char *p;
    
    checkHeap();
    p = malloc(size);
    p[0] = i;
    p[size-1] = i;
    checkHeap();
    free(p);
  }

  // this one will detect a trashed a zone, so do it first
  checkHeap();
  expectFail(offEndCheck);
  printf("after offEndCheck\n");

  // now, don't do checkHeap anymore, since it would fail

  expectFail(offEnd);
  expectFail(offBeg);
  ok();
  expectFail(dangle);
  expectFail(doubleFree);

  printf("tmalloc works\n");
  return 0;
}
