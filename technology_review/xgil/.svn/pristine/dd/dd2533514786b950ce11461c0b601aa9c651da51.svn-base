// taillist_test.cc; see License.txt for copyright and terms of use

// test code for taillist
#include "taillist.h"
#include "test.h" // USUAL_MAIN

void entry()
{
  int a = 2,b = 4,c = 8,d = 16, e = 42;

  TailList<int> list;

  list.append(&d);
  list.prepend(&b);		// 4, 16
  list.insertAt(&c,1); 		// 4, 8, 16
  list.append(&e); 		// 4, 8, 16, 42
  
  list.removeLast();		// 4, 8, 16

  xassert( list.count() == 3 &&
	   !list.isEmpty() &&
	   list.nth(0) == &b &&
	   list.nth(1) == &c &&
	   list.nth(2) == &d &&
	   list.indexOf(&b) == 0 &&
	   list.indexOf(&c) == 1 &&
	   list.indexOf(&e) == -1 &&
	   list.indexOf(&d) == 2
	   );
  
  // FIX: the selfCheck routine in the VoidTailList superclass is broken. 
  // list.selfCheck();
  
  list.prepend(&a);		// 2, 4, 8, 16
  
  int count = 2;
  FOREACH_TAILLIST_NC(int,list, iter) {
    xassert( *(iter.data()) == count);
    count *= 2;
  }

}

USUAL_MAIN
