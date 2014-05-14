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

#ifndef __SAT_SOLVER__
#define __SAT_SOLVER__

#include "zchaff_version.h"
#include "zchaff_dbase.h"

#ifndef _SAT_STATUS_
#define _SAT_STATUS_

enum SAT_StatusT {
  UNDETERMINED,
  UNSATISFIABLE,
  SATISFIABLE,
  TIME_OUT,
  MEM_OUT,
  ABORTED
};
#endif

enum SAT_DeductionT {
  CONFLICT,
  NO_CONFLICT
};

class CSolver;

typedef void(*HookFunPtrT)(void *) ;
typedef void(*OutsideConstraintHookPtrT)(CSolver * solver);
typedef bool(*SatHookPtrT)(CSolver * solver);

// **Struct********************************************************************
//
//  Synopsis    [Sat solver parameters ]
//
//  Description []
//
//  SeeAlso     []
//
// ****************************************************************************

struct CSolverParameters {
  float         time_limit;
  int           verbosity;

  struct {
    unsigned    size;
    int         enable;
    int         upper_bound;
    int         lower_bound;
    int         upper_delta;
    int         lower_delta;
    int         bound_update_frequency;
    unsigned    window_width;
  } shrinking;

  struct {
    int         base_randomness;
    int         bubble_init_step;
    int         decay_period;
  } decision;

  struct {
    bool        enable;
    unsigned    interval;
    unsigned    head_activity;
    unsigned    tail_activity;
    unsigned    head_num_lits;
    unsigned    tail_num_lits;
    int         tail_vs_head;
  } cls_deletion;

  struct {
    bool        enable;
    int         interval;
    int         first_restart;
    int         backtrack_incr;
  } restart;
};

// **Struct********************************************************************
//
//  Synopsis    [Sat solver statistics ]
//
// Description []
//
//  SeeAlso     []
//
// ****************************************************************************

struct CSolverStats {
  bool          been_reset;  // when delete clause in incremental solving,
                             // must reset.
  SAT_StatusT   outcome;
  bool          is_mem_out;  // this flag will be set if memory out
  double        start_cpu_time;
  double        finish_cpu_time;
  int           current_randomness;
  int           next_restart;
  int           restart_incr;
  int           next_cls_deletion;
  int           next_var_score_decay;
  int           num_free_variables;
  int           num_free_branch_vars;
  long64        total_bubble_move;
  int           num_decisions;
  int           num_decisions_stack_conf;
  int           num_decisions_vsids;
  int           num_decisions_shrinking;
  int           num_shrinkings;
  int           shrinking_benefit;
  int           shrinking_cls_length;
  int           num_backtracks;
  int           max_dlevel;
  int           random_seed;
  long64        num_implications;
  int           num_restarts;
  int           num_del_orig_cls;
};

// **Class*********************************************************************
//
//  Synopsis    [Sat Solver]
//
//  Description [This class contains the process and datastructrues to solve
//               the Sat problem.]
//
//  SeeAlso     []
//
// ****************************************************************************

inline bool cmp_var_stat(const pair<CVariable *, int> & v1,
                         const pair<CVariable *, int> & v2) {
  return v1.second >= v2.second;
}

struct cmp_var_assgn_pos {
  bool operator() (CVariable * v1, CVariable * v2) {
    if (v1->dlevel() > v2->dlevel())
      return true;
    else if (v1->dlevel() < v2->dlevel())
      return false;
    else if (v1->assgn_stack_pos() > v2->assgn_stack_pos())
      return true;
    return false;
  }
};

struct CImplication {
  int lit;
  int antecedent;
};

struct ImplicationQueue:queue<CImplication> {
  void dump(ostream & os) {
    queue<CImplication> temp(*this);
    os << "Implication Queue Previous: " ;
    while (!temp.empty()) {
      CImplication a = temp.front();
      os << "(" << ((a.lit & 0x1) ? "-" : "+") << (a.lit >> 1)
         << ":" << a.antecedent << ")  ";
      temp.pop();
    }
  }
};

class CSolver:public CDatabase {
  protected:
    int                 _id;                  // the id of the solver, in case
                                              // we need to distinguish
    bool                _force_terminate;
    CSolverParameters   _params;              // parameters for the solver
    CSolverStats        _stats;               // statistics and states

    int                 _dlevel;              // current decision elvel
    vector<vector<int>*>_assignment_stack;
    queue<int>          _recent_shrinkings;
    bool                _mark_increase_score;  // used in mark_vars during
                                              // multiple conflict analysis
    long64              _implication_id;
    ImplicationQueue    _implication_queue;

    // hook function run after certain number of decisions
    vector<pair<int, pair<HookFunPtrT, int> > > _hooks;
    OutsideConstraintHookPtrT                   _outside_constraint_hook;
    SatHookPtrT         _sat_hook;  // hook function run after a satisfiable
                                    // solution found, return true to continue
                              // solving and false to terminate as satisfiable

    // these are for decision making
    int                 _max_score_pos;   // index the unassigned var with
                                          // max score
    vector<pair<CVariable*, int> > _ordered_vars;  // pair's first pointing to
                                              // the var, second is the score.

    // these are for conflict analysis
    int               _num_marked;     // used when constructing learned clause
    int               _num_in_new_cl;  // used when constructing learned clause
    vector<ClauseIdx> _conflicts;      // the conflicting clauses
    vector<int>       _conflict_lits;  // used when constructing learned clause
    vector<int>       _resolvents;
    multimap<int, int> _shrinking_cls;

  protected:
    void re_init_stats(void);
    void init_stats(void);
    void init_parameters(void);
    void init_solve(void);
    void real_solve(void);
    void restart(void);
    int preprocess(void);
    int deduce(void);
    void run_periodic_functions(void);

    // for decision making
    bool decide_next_branch(void);
    void decay_variable_score(void) ;
    void adjust_variable_order(int * lits, int n_lits);
    void update_var_score(void);

    // for conflict analysis
    ClauseIdx add_conflict_clause(int * lits, int n_lits, int gflag);
    int analyze_conflicts(void);
    ClauseIdx finish_add_conf_clause(int gflag);
    int conflict_analysis_firstUIP(void);
    void mark_vars(ClauseIdx cl, int var_idx);
    void back_track(int level);

    // for bcp
    void set_var_value(int var, int value, ClauseIdx ante, int dl);
    void set_var_value_BCP(int v, int value);
    void unset_var_value(int var);

    // misc functions
    bool time_out(void);
    void delete_unrelevant_clauses(void);
    ClauseIdx add_clause_with_gid(int * lits, int n_lits, int gid = 0);

  public:
    // constructors and destructors
    CSolver(void);
    ~CSolver(void);

    // member access function
    void set_time_limit(float t);
    void set_mem_limit(int s);
    void enable_cls_deletion(bool allow);
    void set_randomness(int n) ;
    void set_random_seed(int seed);

    void set_variable_number(int n);
    int add_variable(void) ;
    void mark_var_branchable(int vid);
    void mark_var_unbranchable(int vid);

    inline int & dlevel(void) {
      return _dlevel;
    }

    inline int outcome(void) {
      return _stats.outcome;
    }

    inline int num_decisions(void) {
      return _stats.num_decisions;
    }

    inline int num_decisions_stack_conf(void) {
      return _stats.num_decisions_stack_conf;
    }

    inline int num_decisions_vsids(void) {
      return _stats.num_decisions_vsids;
    }

    inline int num_decisions_shrinking(void) {
      return _stats.num_decisions_shrinking;
    }

    inline int num_shrinkings(void) {
      return _stats.num_shrinkings;
    }

    inline int & num_free_variables(void) {
      return _stats.num_free_variables;
    }

    inline int max_dlevel(void) {
      return _stats.max_dlevel;
    }

    inline int random_seed(void) {
      return _stats.random_seed;
    }

    inline long64 num_implications(void) {
      return _stats.num_implications;
    }

    inline long64 total_bubble_move(void) {
      return _stats.total_bubble_move;
    }

    inline const char * version(void) {
      return __ZCHAFF_VERSION__;
    }

    float elapsed_cpu_time(void);
    float cpu_run_time(void) ;
    int estimate_mem_usage(void) {
      return CDatabase::estimate_mem_usage();
    }

    int mem_usage(void);

    void queue_implication(int lit, ClauseIdx ante_clause) {
      CImplication i;
      i.lit = lit;
      i.antecedent = ante_clause;
      _implication_queue.push(i);
    }

    // top level function
    inline int id(void) {
      return _id;
    }

    inline void set_id(int i) {
      _id = i;
    }

    inline void force_terminate(void) {
      _force_terminate = true;
    }

    inline void unset_force_terminate(void) {
      _force_terminate = false;
    }

    // for incremental SAT
    int add_clause_incr(int * lits, int n_lits, int gid = 0);

    void make_decision(int lit) {
        ++dlevel();
        queue_implication(lit, NULL_CLAUSE);
    }

    void add_hook(HookFunPtrT fun, int interval);

    inline void add_outside_constraint_hook(OutsideConstraintHookPtrT fun) {
      _outside_constraint_hook = fun;
    }

    inline void add_sat_hook(SatHookPtrT fun) {
      _sat_hook = fun;
    }

    void verify_integrity(void);
    void delete_clause_group(int gid);
    void reset(void);
    int solve(void);
    ClauseIdx add_orig_clause(int * lits, int n_lits, int gid = 0);
    void clean_up_dbase(void);
    void dump_assignment_stack(ostream & os = cout);
    void dump_implication_queue(ostream & os = cout);

    void print_cls(ostream & os = cout);
    void dump(ostream & os = cout ) {
        CDatabase::dump(os);
        dump_assignment_stack(os);
    }
    void add_outside_clauses(void);
};
#endif
