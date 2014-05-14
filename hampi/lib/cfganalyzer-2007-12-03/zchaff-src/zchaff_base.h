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
//  any trademark, service mark, or the name of Princeton University.
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


#ifndef __BASIC_CLASSES__
#define __BASIC_CLASSES__

#include <assert.h>

#include "zchaff_header.h"

#define UNKNOWN           2
#define NULL_CLAUSE          -1

#define VOLATILE_GID   -1
#define        PERMANENT_GID         0
// #define KEEP_LIT_CLAUSES
typedef int ClauseIdx;  // Used to refer a clause. Because of dynamic
                        // allocation of vector storage, no pointer is allowered

#ifndef _CLS_STATUS_
#define _CLS_STATUS_
enum CLAUSE_STATUS {
  ORIGINAL_CL,
  CONFLICT_CL,
  DELETED_CL,
};
#endif

// /**Class********************************************************************
//
//   Synopsis    [Definition of a literal]
//
//   Description [A literal is a variable with phase. Two things specify a
//                literal: its "sign", and its variable index.
//
//                Each clause that has more than 1 literal contains two special
//                literals. They are being "watched". A literal is marked with
//                2 bits: 00->not watched; 11->watched, direction = 1;
//                01->watched, dir = -1; 10 is not valid. These two bits occupy
//                the least significant bits of the literal.
//
//                Each literal is represented by a 32 bit signed integer. The
//                higher 29 bits represent the variable index. At most 2**28
//                varialbes are allowed. If the sign of this integer is
//                negative, it means that it is not a valid literal. It could
//                be a clause index or a deleted literal pool element. The 3rd
//                least significant bit is used to mark its sign.
//                0->positive, 1->negative.
//
//                The literals are collected in a storage space called literal
//                pool. An element in a literal pool can be a literal or a
//                special spacing element to indicate the termination of a
//                clause. The spacing elements has negative value of the clause
//                index.]
//
//                Right Hand spacing element has the clause id, so why is it
//                not less than 0?
//
//   SeeAlso     [CDatabase, CClause]
//
// ****************************************************************************

class CLitPoolElement {
  protected:
    int32 _val;

  public:
    // constructors & destructors
    CLitPoolElement(void):_val(0)        {}

    ~CLitPoolElement()                         {}

    // member access function
    int & val(void) {
      return _val;
    }

    // stands for signed variable, i.e. 2*var_idx + sign
    int s_var(void) {
      return _val >> 2;
    }

    unsigned var_index(void) {
      return _val >> 3;
    }

    unsigned var_sign(void) {
      return ((_val >> 2) & 0x1);
    }

    void set(int s_var) {
      _val = (s_var << 2);
    }

    void set(int vid, int sign) {
      _val = (((vid << 1) + sign) << 2);
    }

    // followings are for manipulate watched literals
    int direction(void) {
      return ((_val & 0x3) - 2);
    }

    bool is_watched(void) {
      return ((_val & 0x3) != 0);
    }

    void unwatch(void) {
      _val = _val & (~0x3);
    }

    void set_watch(int dir) {
      _val = _val + dir + 2;
    }

    // following are used for spacing (e.g. indicate clause's end)
    bool is_literal(void) {
      return _val > 0;
    }

    void set_clause_index(int cl_idx) {
      _val = - cl_idx;
    }

    ClauseIdx get_clause_index(void) {
      assert(_val <= 0);
      return -_val;
    }

    // misc functions
    unsigned find_clause_index(void) {
      CLitPoolElement * ptr;
      for (ptr = this; ptr->is_literal(); ++ptr);
      return ptr->get_clause_index();
    }

    // every class should have a dump function and a self check function
    void dump(ostream & os= cout);

    friend ostream & operator << (ostream & os, CLitPoolElement & l) {
      l.dump(os);
      return os;
    }
};

// /**Class********************************************************************
//
//   Synopsis    [Definition of a clause]
//
//   Description [A clause is consisted of a certain number of literals.
//                All literals are collected in a single large vector, called
//                literal pool. Each clause has a pointer to the beginning
//                position of it's literals in the pool.
//
//                Zchaff support incremental SAT. Clauses can be added or
//                deleted from the database during search. To accomodate this
//                feature, some modifications are needed.
//
//                Clauses can be generated during search by conflict driven
//                analysis. Conflict clauses are generated by a resolution
//                process. Therefore, if after one search, some clauses got
//                deleted, then some of the learned conflict clause may be
//                invalidated. To maintain the integrity of the clause
//                database, it is necessary to keep track of the clauses that
//                are involved in the resolution process for a certain conflict
//                clause so that when those clauses are deleted, the conflict
//                clause should also be deleted.
//
//                The scheme we implement is similar to the scheme described in
//                : Ofer Strichman, Pruning techniques for the SAT-based
//                Bounded Model Checking Problems, in Proc. 11th Advanced
//                Research Working Conference on Correct Hardware Design and
//                Verification Methods (CHARME'01)
//                ]
//
//   SeeAlso     [CDatabase]
//
// ****************************************************************************
class CClause {
  protected:
    CLitPoolElement *   _first_lit;     // pointer to the first literal
    unsigned            _num_lits ;
    CLAUSE_STATUS       _status : 3;
    unsigned            _id     : 29;   // the unique ID of a clause
    unsigned            _gflag;         // the clause group id flag,
                                        // maximum allow WORD_WIDTH groups
    int                 _activity;
    int                 _sat_lit_idx;

  public:

    // constructors & destructors
    CClause(void) {
      _sat_lit_idx = 0;
    }

    ~CClause() {}

    // initialization & clear up
    void init(CLitPoolElement * head, unsigned num_lits, unsigned gflag) {
      _first_lit = head;
      _num_lits = num_lits;
      _gflag = gflag;
    }

    // member access function
    inline int & activity(void) {
      return _activity;
    }

    inline int & sat_lit_idx(void) {
      return _sat_lit_idx;
    }

    inline CLitPoolElement * literals(void) {
      // literals()[i] is it's the i-th literal
      return _first_lit;
    }

    // return the idx-th literal
    inline CLitPoolElement & literal(int idx) {
     return *(_first_lit + idx);
    }

    // use it only if you want to modify _first_lit
    inline CLitPoolElement * & first_lit(void) {
      return _first_lit;
    }

    inline unsigned & num_lits(void) {
      return _num_lits;
    }

    inline unsigned id(void) {
      return _id;
    }

    inline void set_id(int id) {
      _id = id;
    }

    inline CLAUSE_STATUS status(void) {
      return _status;
    }

    inline void set_status(CLAUSE_STATUS st) {
      _status = st;
    }

    // manipulate the group flag
    inline unsigned & gflag(void) {
      return _gflag;
    }

    inline bool gid(int i) {
      assert(i >= 1 && i <= WORD_WIDTH);
      return ((_gflag & (1 << (i - 1))) != 0);
    }

    inline void set_gid(int i) {
      assert(i >= 1 && i <= WORD_WIDTH);
      _gflag |= (1 << (i - 1));
    }

    inline void clear_gid(int i) {
      assert(i >= 1 && i <= WORD_WIDTH);
      _gflag &= ~(1 << (i - 1));
    }

    // misc function
    bool self_check(void);

    void dump(ostream & os = cout);

    friend ostream & operator << (ostream & os, CClause & cl) {
        cl.dump(os);
        return os;
    }
};


// /**Class********************************************************************
//
// Synopsis    [Definition of a variable]
//
// Description [CVariable contains the necessary information for a variable.]
//
// SeeAlso     [CDatabase]
//
// ****************************************************************************
class CVariable {
  protected:
    unsigned _value             : 2;  // it can take 3 values, 0, 1 and UNKNOWN
    bool _marked                : 1;  // used in conflict analysis.
    unsigned _new_cl_phase      : 2;  // it can take 3 value
    // 0: pos phase, 1: neg phase, UNKNOWN : not in new clause;
    // It is used to keep track of literals appearing
    // in newly added clause so that
    // a. each variable can only appearing in one phase
    // b. same literal won't appear more than once.
    bool _enable_branch         : 1;  // if this variable is enabled in branch
                                      // selection
    int _implied_sign           : 1;  // when a var is implied, here is the
                                      // sign (1->negative, 0->positive)
    ClauseIdx _antecedent;    // used in conflict analysis.
    int _dlevel;              // decision level this variable being assigned
    int _assgn_stack_pos;     // the position where it is in the assignment
                              // stack
    int _lits_count[2];       // how many literals are there with this
                              // variable. (two phases)
    int _2_lits_count[2];     // how many literals in 2 literal clauses are
                              // there with this variable. (two phases)
    vector<CLitPoolElement *> _watched[2];  // watched literals of this
                                            // var. 0: pos phase, 1: neg phase

#ifdef KEEP_LIT_CLAUSES
    vector<ClauseIdx> _lit_clauses[2];  // this will keep track of ALL the
                                        // appearance of the variable in
                                        // clauses
                                        // note this will increase the database
                                        // size by upto a factor of 2
#endif
    int _scores[2];                     // the score used for decision making
    int _var_score_pos;                 // keep track of this variable's
                                        // position in the sorted score array

  public:
    // constructors & destructors
    CVariable(void) {
        init();
        _lits_count[0] = _lits_count[1] = 0;
        _2_lits_count[0] = _2_lits_count[1] = 0;
    }

    ~CVariable() {}

    void init(void) {
      _value = UNKNOWN;
      _antecedent = NULL_CLAUSE;
      _marked = false;
      _dlevel = -1;
      _assgn_stack_pos = -1;
      _new_cl_phase = UNKNOWN;
      _scores[0] = _scores[1] = 0;
      _enable_branch = true;
    }

    // member access function
    inline int & score(int i) {
      return _scores[i];
    }

    inline int & two_lits_count(int i) {
      return _2_lits_count[i];
    }

    inline int score(void) {
      // return 1; this will make a fixed order branch heuristic
      int result = score(0) > score(1) ? score(0) : score(1);
      if (_dlevel == 0)
        result =-1;
      return result;
    }

    inline int & var_score_pos(void) {
      return _var_score_pos;
    }

    inline void set_var_score_pos(int pos) {
      _var_score_pos = pos;
    }

    inline unsigned value(void) {
      return _value;
    }

    inline void set_value(unsigned v) {
      _value = v;
    }

    inline int & dlevel(void) {
      return _dlevel;
    }

    inline int get_dlevel(void) {
      return _dlevel;
    }

    inline void set_dlevel(int dl) {
      _dlevel = dl;
    }

    inline int & assgn_stack_pos(void) {
      return _assgn_stack_pos;
    }

    inline int & lits_count(int i) {
      return _lits_count[i];
    }

    inline bool is_marked(void) {
      return _marked;
    }

    inline int get_implied_sign(void) {
      return _implied_sign;
    }

    inline void set_implied_sign(int sign) {
      _implied_sign = sign;
    }

    inline unsigned new_cl_phase(void) {
      return _new_cl_phase;
    }

    inline void set_new_cl_phase(unsigned phase) {
      _new_cl_phase = phase;
    }

    inline void set_marked(void) {
      _marked = true;
    }

    inline void clear_marked(void) {
      _marked = false;
    }

    inline ClauseIdx & antecedent(void) {
      return _antecedent;
    }

    inline ClauseIdx get_antecedent(void) {
      return _antecedent;
    }

    inline void set_antecedent(ClauseIdx cl) {
      _antecedent = cl;
    }

    inline vector<CLitPoolElement *> & watched(int i) {
      return _watched[i];
    }

    inline void enable_branch(void) {
      _enable_branch = true;
    }

    inline void disable_branch(void) {
      _enable_branch = false;
    }

    inline bool is_branchable(void) {
      return _enable_branch;
    }

#ifdef KEEP_LIT_CLAUSES
    inline vector<ClauseIdx> & lit_clause(int i) {
      return _lit_clauses[i];
    }
#endif

    // misc function
    bool self_check(void);

    void dump(ostream & os = cout);

    friend ostream & operator << (ostream & os, CVariable & v) {
      v.dump(os);
      return os;
    }
};
#endif
