// tarrayqueue.cc
// test arrayqueue.h module

#include "arrayqueue.h"      // module to test
#include "objlist.h"         // ObjList
#include "ckheap.h"          // malloc_stats

#include <stdio.h>           // printf
#include <stdlib.h>          // exit


int maxLength = 0;

// one round of testing
void round(int ops)
{
  // implementation to test
  ArrayQueue<int> arrayQueue;

  // "trusted" implementation to compare with
  ObjList<int> listQueue;

  while (ops--) {
    // check that the array and list agree
    {
      int index = 0;
      FOREACH_OBJLIST(int, listQueue, iter) {
        xassert(iter.data()[0] == arrayQueue[index]);
        index++;
      }
      xassert(index == arrayQueue.length());
      xassert(arrayQueue.isEmpty() == listQueue.isEmpty());
      xassert(arrayQueue.isNotEmpty() == listQueue.isNotEmpty());
      
      if (index > maxLength) {
        maxLength = index;
      }
    }

    // do a random operation
    int op = rand() % 100;
    if (op == 0) {
      // empty the queues
      arrayQueue.empty();
      listQueue.deleteAll();
    }
    else if (op < 5) {
      // reverse them
      arrayQueue.reverse();
      listQueue.reverse();
    }
    else if (op < 40 && arrayQueue.isNotEmpty()) {
      // dequeue
      int i = arrayQueue.dequeue();
      int *j = listQueue.removeFirst();
      xassert(i == *j);
      delete j;
    }
    else {
      // enqueue
      int elt = rand() % 100;
      arrayQueue.enqueue(elt);
      listQueue.append(new int(elt));
    }
  }
}


int main()
{
  for (int i=0; i<20; i++) {
    round(1000);
  }

  malloc_stats();
  printf("arrayqueue appears to work; maxLength=%d\n", maxLength);
  return 0;
}


// EOF
