// *********************************************************************
// Copyright 2000-2004, Princeton University.  All rights reserved.
// By using this software the USER indicates that he or she has read,
// understood and will comply with the following:
//
// --- Princeton University hereby grants USER nonexclusive permission
// to use, copy and/or modify this software for internal, noncommercial,
// research purposes only. Any distribution, including commercial sale
// or license, of this software, copies of the software, its associated
// documentation and/or modifications of either is strictly prohibited
// without the prior consent of Princeton University.  Title to copyright
// to this software and its associated documentation shall at all times
// remain with Princeton University.  Appropriate copyright notice shall
// be placed on all software copies, and a complete copy of this notice
// shall be included in all copies of the associated documentation.
// No right is  granted to use in advertising, publicity or otherwise
// any trademark,  service mark, or the name of Princeton University.
//
//
// --- This software and any associated documentation is provided "as is"
//
// PRINCETON UNIVERSITY MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS
// OR IMPLIED, INCLUDING THOSE OF MERCHANTABILITY OR FITNESS FOR A
// PARTICULAR PURPOSE, OR THAT  USE OF THE SOFTWARE, MODIFICATIONS, OR
// ASSOCIATED DOCUMENTATION WILL NOT INFRINGE ANY PATENTS, COPYRIGHTS,
// TRADEMARKS OR OTHER INTELLECTUAL PROPERTY RIGHTS OF A THIRD PARTY.
//
// Princeton University shall not be liable under any circumstances for
// any direct, indirect, special, incidental, or consequential damages
// with respect to any claim by USER or any third party on account of
// or arising from the use, or inability to use, this software or its
// associated documentation, even if Princeton University has been advised
// of the possibility of those damages.
// *********************************************************************

#ifndef __CLAUSE_GENERATOR__
#define __CLAUSE_GENERATOR__
#include "zchaff_solver.h"

class CClause_Gen {
  private:
    inline static int * ptr(vector<int>::iterator itr) {
      return &(*itr);
    }
    inline static int pos(int i) {
      return i;
    }
    inline static int neg(int i) {
      return i^0x1;
    }

  public:
    static void and2(CSolver & solver, int a, int b, int o, int gid = 0) {
      // a*b=c <==> (a + o')( b + o')(a'+b'+o)
      vector <int> lits;
      lits.clear();
      lits.push_back(pos(a));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(pos(b));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(neg(a));
      lits.push_back(neg(b));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }

    static void and_n(CSolver & solver, int * inputs, int num_input, int o,
                      int gid = 0) {
      vector <int> lits;
      int i;
      for (i = 0; i < num_input; ++i) {
        lits.clear();
        lits.push_back(pos(inputs[i]));
        lits.push_back(neg(o));
        solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      }
      lits.clear();
      for (i = 0; i < num_input; ++i)
        lits.push_back(neg(inputs[i]));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }

    static void or2(CSolver & solver, int a, int b, int o, int gid = 0) {
      // a+b=c <==> (a' + c)( b' + c)(a + b + c')
      vector <int> lits;
      lits.clear();
      lits.push_back(neg(a));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(neg(b));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(pos(a));
      lits.push_back(pos(b));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }

    static void or_n(CSolver & solver, int * inputs, int num_input, int o,
                     int gid = 0) {
      vector <int> lits;
      int i;
      for (i = 0; i < num_input; ++i) {
        lits.clear();
        lits.push_back(neg(inputs[i]));
        lits.push_back(pos(o));
        solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      }
      lits.clear();
      for (i = 0; i < num_input; ++i)
        lits.push_back(pos(inputs[i]));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }

    static void nand2(CSolver & solver, int a, int b, int o, int gid = 0) {
      // a Nand b = o <==> (a + o)( b + o)(a' + b' + o')
      vector <int> lits;
      lits.clear();
      lits.push_back(pos(a));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(pos(b));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(neg(a));
      lits.push_back(neg(b));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }

    static void nand_n(CSolver & solver, int * inputs, int num_input, int o,
                       int gid = 0) {
      vector <int> lits;
      int i;
      for (i = 0; i < num_input; ++i) {
        lits.clear();
        lits.push_back(pos(inputs[i]));
        lits.push_back(pos(o));
        solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      }
      lits.clear();
      for (i = 0; i < num_input; ++i)
        lits.push_back(neg(inputs[i]));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }

    static void nor2(CSolver & solver, int a, int b, int o, int gid = 0) {
      // a Nor b = o <==> (a' + o')( b' + o')(a + b + o)
      vector <int> lits;
      lits.clear();
      lits.push_back(neg(a));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(neg(b));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(pos(a));
      lits.push_back(pos(b));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }

    static void nor_n(CSolver & solver, int * inputs, int num_input, int o,
               int gid = 0) {
      vector <int> lits;
      int i;
      for (i = 0; i < num_input; ++i) {
        lits.clear();
        lits.push_back(neg(inputs[i]));
        lits.push_back(neg(o));
        solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      }
      lits.clear();
      for (i = 0; i < num_input; ++i)
        lits.push_back(pos(inputs[i]));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }

    static void xor2(CSolver & solver, int a, int b, int o, int gid = 0) {
      // a xor b = o <==> (a' + b' + o')
      //                  (a + b + o' )
      //                  (a' + b + o)
      //                         (a + b' + o)
      vector <int> lits;
      lits.clear();
      lits.push_back(neg(a));
      lits.push_back(neg(b));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(pos(a));
      lits.push_back(pos(b));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(neg(a));
      lits.push_back(pos(b));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(pos(a));
      lits.push_back(neg(b));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }

    static void not1(CSolver & solver, int a, int o, int gid = 0) {
      // a' = o <==> (a' + o')( a + o)
      vector <int> lits;
      lits.clear();
      lits.push_back(neg(a));
      lits.push_back(neg(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
      lits.clear();
      lits.push_back(pos(a));
      lits.push_back(pos(o));
      solver.add_orig_clause(ptr(lits.begin()), lits.size(), gid);
    }
};
#endif
