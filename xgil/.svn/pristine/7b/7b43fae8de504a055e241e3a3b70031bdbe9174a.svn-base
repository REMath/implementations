// implint.cc            see license.txt for copyright and terms of use
// implicit-int parsing support routines

// this doesn't include implint.h b/c that's sort of different

#include "cc_ast.h"       // AST
#include "trace.h"        // trace
#include "array.h"        // Array


// Mutate 'params' filtering out any alternatives of the first param
// (if there is one) that are of type implicit-int.  Return true if
// we should really construct a D_func that the grammar rule wants
// to construct.
bool filterOutImplIntFirstParam
  (SourceLoc loc,
   IDeclarator *base,
   FakeList<ASTTypeId> *&params) {
  // skip unless are we an anonymous function with at least one
  // parameter
  if (! (base->isD_name() && !base->asD_name()->name && params && params->first())) {
    return true;                // keep it
  }

  // dsw: remove all of the alternatives for the first parameter
  // that are of type implicit-int; NOTE: this may be wrong in some
  // strange circumstance where a preceeding const/volatile/register
  // keyword makes the implicit-int legal.  To attempt to emulate
  // that would complicate the code even more so I don't until we
  // see a real example so at least we have something real to test
  // against.

  // NOTE: this is a mutating walk over a linked list, which is
  // really error-prone; therefore I do the easy thing and copy it
  // to another list and copy it back; this problem alone is reason
  // enough not to use linked lists

  // count the ambiguities
  // NOTE: do NOT do this!  It is wrong: It counts the parameters.
  //        int numAlt = params->count();
  int numAlt = 0;
  for (ASTTypeId *atid = params->first(); atid; atid = atid->ambiguity) {
    ++numAlt;
  }

  // make a temporary array
  Array<ASTTypeId*> tempList(numAlt);

  // put them in there
  int i = 0;
  for (ASTTypeId *atid = params->first(); atid; atid = atid->ambiguity, ++i) {
    tempList[i] = atid;
  }

  // remove the ambiguity pointers
  for (i=0; i<numAlt; ++i) {
    tempList[i]->ambiguity = NULL;
  }

  // remove the implicit-int possibilities
  for (i=0; i<numAlt; ++i) {
    ASTTypeId *atid = tempList[i];
    if (atid->spec->isTS_simple() &&
        atid->spec->asTS_simple()->id == ST_IMPLINT) {
      trace("cancel") << loc << ": implicit-int function first param\n";
      tempList[i] = NULL;
    }
  }

  // rebuild a linked list from those that remain
  ASTTypeId *newList = NULL;
  for (i=0; i<numAlt; ++i) {
    if (tempList[i]) {
      tempList[i]->ambiguity = newList;
      newList = tempList[i];
    }
  }

  // NOTE: this will be in reverse order
  params = FakeList<ASTTypeId>::makeList(newList);

  // keep the D_func iff there are alternatives left for the first
  // parameter; NOTE: Do NOT do 'return params->isNotEmpty()'; that
  // returns the number of parameters, not the number of surviving
  // ambiguous alternatives
  return newList;
}


// EOF
