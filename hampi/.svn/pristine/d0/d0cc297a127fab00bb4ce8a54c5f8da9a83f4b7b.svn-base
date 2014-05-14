// /*********************************************************************
//  Copyright 2000-2004, Princeton University.  All rights reserved.
//  By using this software the USER indicates that he or she has read,
//  understood and will comply with the following:
//
//  --- Princeton University hereby grants USER nonexclusive permission
//  to use, copy and/or modify this software for internal, noncommercial,
//  research purposes only. Any distribution, including commercial sale
//  or license, of this software, copies of the software, its associated
//  documentation and/or modifications of either is strictly prohibited
//  without the prior consent of Princeton University.  Title to copyright
//  to this software and its associated documentation shall at all times
//  remain with Princeton University.  Appropriate copyright notice shall
//  be placed on all software copies, and a complete copy of this notice
//  shall be included in all copies of the associated documentation.
//  No right is  granted to use in advertising, publicity or otherwise
//  any trademark,  service mark, or the name of Princeton University.
//
//
//  --- This software and any associated documentation is provided "as is"
//
//  PRINCETON UNIVERSITY MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS
//  OR IMPLIED, INCLUDING THOSE OF MERCHANTABILITY OR FITNESS FOR A
//  PARTICULAR PURPOSE, OR THAT  USE OF THE SOFTWARE, MODIFICATIONS, OR
//  ASSOCIATED DOCUMENTATION WILL NOT INFRINGE ANY PATENTS, COPYRIGHTS,
//  TRADEMARKS OR OTHER INTELLECTUAL PROPERTY RIGHTS OF A THIRD PARTY.
//
//  Princeton University shall not be liable under any circumstances for
//  any direct, indirect, special, incidental, or consequential damages
//  with respect to any claim by USER or any third party on account of
//  or arising from the use, or inability to use, this software or its
//  associated documentation, even if Princeton University has been advised
//  of the possibility of those damages.
// *********************************************************************/

#include <iostream>
#include <vector>

using namespace std;

#include "zchaff_base.h"

void CLitPoolElement::dump(ostream & os) {
  os << (var_sign() ? " -" : " +") << var_index();
  if (is_watched())
    os << "*";
}

void CClause::dump(ostream & os) {
  if (status() == DELETED_CL)
    os << "\t\t\t======removed=====";
  for (int i = 0, sz = num_lits(); i < sz; ++i)
    os << literal(i);
  os << endl;
}

bool CClause::self_check(void) {
  assert(num_lits() > 0);
  int watched = 0;
  for (unsigned i = 0; i < num_lits(); ++i) {
    assert(literal(i).is_literal());
    if (literal(i).is_watched())
      ++watched;
  }
  assert(num_lits() ==1 || watched == 2);  // either unit, or have two watched
  assert(!literal(num_lits() + 1).is_literal());
  return true;
}

bool CVariable::self_check(void) {
  for (unsigned i = 0; i < 2; ++i) {
    vector<CLitPoolElement*>& w = watched(i);
    for (unsigned j = 0; j < w.size(); ++j) {
      assert(w[j]->is_watched());
      assert((unsigned)w[j]->var_sign() == i);
    }
  }
  return true;
}

void CVariable::dump(ostream & os) {
  if (is_marked())
    os << "*" ;
  os << "V: " << _value << "  DL: " << _dlevel  << "  POS: "<< _assgn_stack_pos
     << "  Ante: " << _antecedent << endl;
  for (unsigned j = 0; j < 2; ++j) {
    os << (j == 0 ? "WPos " : "WNeg ") <<  "(" ;
    for (unsigned i = 0; i < watched(j).size(); ++i)
      os << watched(j)[i]->find_clause_index() << "  " ;
    os << ")" << endl;
  }
#ifdef KEEP_LIT_CLAUSES
  for (unsigned j = 0; j < 2; ++j) {
    os << (j == 0 ? "Pos " : "Neg ") <<  "(" ;
    for (unsigned i = 0; i < lit_clause(j).size(); ++i)
      os << lit_clause(j)[i] << "  " ;
    os << ")" << endl;
  }
#endif
  os << endl;
}
