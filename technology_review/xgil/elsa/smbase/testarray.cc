// testarray.cc
// test the array.h module
// based on tarrayqueue.cc

#include "array.h"     // module to test
#include "objlist.h"         // ObjList
#include "ckheap.h"          // malloc_stats

#include <stdio.h>           // printf
#include <stdlib.h>          // exit


int maxLength = 0;

// one round of testing
void round(int ops)
{
  // implementations to test
  ArrayStack<int> arrayStack;
  ArrayStackEmbed<int, 10> arrayStackEmbed;

  // "trusted" implementation to compare with
  ObjList<int> listStack;

  while (ops--) {
    // check that the arrays and list agree
    {
      int length = listStack.count();
      if (length > 0) {
        xassert(listStack.first()[0] == arrayStack.top());
        xassert(listStack.first()[0] == arrayStackEmbed.top());
      }

      int index = length-1;
      FOREACH_OBJLIST(int, listStack, iter) {
        xassert(iter.data()[0] == arrayStack[index]);
        xassert(iter.data()[0] == arrayStackEmbed[index]);
        index--;
      }
      xassert(index == -1);
      xassert(length == arrayStack.length());
      xassert(length == arrayStackEmbed.length());
      xassert(arrayStack.isEmpty() == listStack.isEmpty());
      xassert(arrayStackEmbed.isEmpty() == listStack.isEmpty());
      xassert(arrayStack.isNotEmpty() == listStack.isNotEmpty());
      xassert(arrayStackEmbed.isNotEmpty() == listStack.isNotEmpty());

      if (length > maxLength) {
        maxLength = length;
      }
    }

    // do a random operation
    int op = rand() % 100;
    if (op < 40 && arrayStack.isNotEmpty()) {
      // pop
      int i = arrayStack.pop();
      int j = arrayStackEmbed.pop();
      int *k = listStack.removeFirst();
      xassert(i == *k);
      xassert(j == *k);
      delete k;
    }
    else {
      // push
      int elt = rand() % 100;
      arrayStack.push(elt);
      arrayStackEmbed.push(elt);
      listStack.prepend(new int(elt));
    }
  }
}


int main()
{
  for (int i=0; i<20; i++) {
    round(1000);
  }

  malloc_stats();
  printf("arrayStack appears to work; maxLength=%d\n", maxLength);
  return 0;
}


// EOF
