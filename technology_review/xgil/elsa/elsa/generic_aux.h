// generic_aux.h
// some templatized routines that used to be in cc_ast_aux.cc,
// but gnu.cc wants to use them too

#include "cc_ast.h"         // C++ AST

 
// generic get/set 'ambiguity'
template <class NODE>
NODE *getAmbiguity(NODE const *n)
{
  return n->ambiguity;
}

template <class NODE>
void setAmbiguity(NODE *n, NODE *newAmbig)
{
  n->ambiguity = newAmbig;
}


// get/set 'ambiguity' for PQName (implemented in cc_ast_aux.cc)
PQName *getAmbiguity(PQName const *n);
void setAmbiguity(PQName *n, PQName *newAmbig);


template <class NODE>
void genericPrintAmbiguities(NODE const *ths, char const *typeName,
                             ostream &os, int indent)
{
  // count the number of alternatives
  int numAlts = 0;
  {
    for (NODE const *p = ths; p != NULL; p = getAmbiguity(p)) {
      numAlts++;
    }
  }

  // print a visually obvious header
  ind(os, indent) << "--------- ambiguous " << typeName << ": "
                  << numAlts << " alternatives ---------\n";

  // walk down the list of ambiguities, printing each one by
  // temporarily nullifying the 'ambiguity' pointer; cast away
  // the constness so I can do the temporary modification
  int ct=0;
  for (NODE *e = const_cast<NODE*>(ths);
       e != NULL;
       e = getAmbiguity(e)) {
    if (ct++ > 0) {
      ind(os, indent) << "---- or ----\n";
    }

    NODE *tempAmbig = getAmbiguity(e);
    setAmbiguity(e, (NODE*)NULL);
    e->debugPrint(os, indent+2);
    setAmbiguity(e, tempAmbig);
  }

  ind(os, indent) << "--------- end of ambiguous " << typeName
                  << " ---------\n";
}


// make sure that all the 'next' fields end up the same
template <class NODE>
void genericCheckNexts(NODE const *main)
{
  for (NODE const *a = main->ambiguity; a != NULL; a = a->ambiguity) {
    xassert(main->next == a->next);
  }
}

// add another ambiguous alternative to 'main', with care given
// to the fact that NODE has 'next' links
template <class NODE>
void genericAddAmbiguity(NODE *main, NODE *alt)
{
  // 'alt' had better not already be on a list (shouldn't be,
  // because it's the RHS argument to merge, which means it's
  // never been yielded to anything)
  xassert(alt->next == NULL);

  // same reasoning for 'ambiguity'
  //xassert(alt->ambiguity == NULL);
  // no, it turns out the RHS could have been yielded if the
  // reduction action is the identity function.. so instead
  // find the last node in the 'alt' list and we'll splice
  // that entire list into 'main's ambiguity list
  NODE *altLast = alt;
  while (altLast->ambiguity) {
    altLast = altLast->ambiguity;

    // the assignment below will only get the first node, so
    // this takes care of the other ones in 'alt'
    altLast->next = main->next;
  }

  if (main->next) {
    // I don't expect 'main' to already be on a list, so I'll
    // make some noise; but I think it will work anyway
    cout << "note: ambiguous " << main->kindName()
         << "node leader is already on a list..\n";
  }

  // if 'main' has been added to a list, add 'alt' also
  alt->next = main->next;

  // finally, prepend 'alt's ambiguity list to 'main's ambiguity list
  altLast->ambiguity = main->ambiguity;
  main->ambiguity = alt;
}


// set the 'next' field of 'main' to 'newNext', with care given
// to possible ambiguities
template <class NODE>
void genericSetNext(NODE *main, NODE *newNext)
{
  // 'main's 'next' should be NULL; if it's not, then it's already
  // on a list, and setting 'next' now will lose information
  xassert(main->next == NULL);
  main->next = newNext;

  // if 'main' has any ambiguous alternatives, set all their 'next'
  // pointers too
  if (main->ambiguity) {
    genericSetNext(main->ambiguity, newNext);     // recursively set them all
  }
}
