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
// ********************************************************************/

#include <cstdlib>

#include <iostream>
#include <vector>
#include <set>

using namespace std;

#include "zchaff_dbase.h"

CDatabase::CDatabase(void) {
  _stats.mem_used_up                 = false;
  _stats.init_num_clauses            = 0;
  _stats.init_num_literals           = 0;
  _stats.num_added_clauses           = 0;
  _stats.num_added_literals          = 0;
  _stats.num_deleted_clauses         = 0;
  _stats.num_del_orig_cls            = 0;
  _stats.num_deleted_literals        = 0;
  _stats.num_enlarge                 = 0;
  _stats.num_compact                 = 0;
  _lit_pool_start = (CLitPoolElement *) malloc(sizeof(CLitPoolElement) *
                                               STARTUP_LIT_POOL_SIZE);
  _lit_pool_finish = _lit_pool_start;
  _lit_pool_end_storage = _lit_pool_start + STARTUP_LIT_POOL_SIZE;
  lit_pool_push_back(0);  // set the first element as a dummy element
  _params.mem_limit = 1024 * 1024 * 1024;  // that's 1 G
  variables()->resize(1);                  // var_id == 0 is never used.
  _allocated_gid                    = 0;
}

CDatabase::~CDatabase(void) {
  free(_lit_pool_start);
}

unsigned CDatabase::estimate_mem_usage(void) {
  unsigned mem_lit_pool = sizeof(CLitPoolElement) * (lit_pool_size() +
                                                     lit_pool_free_space());
  unsigned mem_vars = sizeof(CVariable) * variables()->capacity();
  unsigned mem_cls = sizeof(CClause) * clauses()->capacity();
  unsigned mem_cls_queue = sizeof(int) * _unused_clause_idx.size();
  unsigned mem_watched = 2 * num_clauses() * sizeof(CLitPoolElement *);
  unsigned mem_lit_clauses = 0;
#ifdef KEEP_LIT_CLAUSES
  mem_lit_clauses = num_literals() * sizeof(ClauseIdx);
#endif
  return (mem_lit_pool + mem_vars + mem_cls +
          mem_cls_queue + mem_watched + mem_lit_clauses);
}

unsigned CDatabase::mem_usage(void) {
  int mem_lit_pool = (lit_pool_size() + lit_pool_free_space()) *
                     sizeof(CLitPoolElement);
  int mem_vars = sizeof(CVariable) * variables()->capacity();
  int mem_cls = sizeof(CClause) * clauses()->capacity();
  int mem_cls_queue = sizeof(int) * _unused_clause_idx.size();
  int mem_watched = 0, mem_lit_clauses = 0;
  for (unsigned i = 0, sz = variables()->size(); i < sz ;  ++i) {
    CVariable & v = variable(i);
    mem_watched        += v.watched(0).capacity() + v.watched(1).capacity();
#ifdef KEEP_LIT_CLAUSES
    mem_lit_clauses += v.lit_clause(0).capacity() + v.lit_clause(1).capacity();
#endif
  }
  mem_watched *= sizeof(CLitPoolElement*);
  mem_lit_clauses *= sizeof(ClauseIdx);
  return (mem_lit_pool + mem_vars + mem_cls +
          mem_cls_queue + mem_watched + mem_lit_clauses);
}

int CDatabase::alloc_gid(void) {
  for (unsigned i = 1; i <= WORD_WIDTH; ++i) {
    if (is_gid_allocated(i) == false) {
      _allocated_gid |= (1 << (i-1));
      return i;
    }
  }
  warning(_POSITION_, "Not enough GID");
  return VOLATILE_GID;
}

void CDatabase::free_gid(int gid) {
  assert(gid > 0 && "Can't free volatile or permanent group");
  assert(gid <= WORD_WIDTH && "gid > WORD_WIDTH?");
  if (!is_gid_allocated(gid)) {
    fatal(_POSITION_, "Can't free unallocated GID");
  }
  _allocated_gid &= (~(1<< (gid-1)));
}

bool CDatabase::is_gid_allocated(int gid) {
  if (gid == VOLATILE_GID || gid == PERMANENT_GID)
    return true;
  assert(gid <= WORD_WIDTH && gid > 0);
  if (_allocated_gid & (1 << (gid -1)))
    return true;
  return false;
}

int CDatabase::merge_clause_group(int g2, int g1) {
  assert(g1 >0 && g2> 0 && "Can't merge with permanent or volatile group");
  assert(g1 != g2);
  assert(is_gid_allocated(g1) && is_gid_allocated(g2));
  for (unsigned i = 0, sz = clauses()->size(); i < sz; ++i) {
    if (clause(i).status() != DELETED_CL) {
      if (clause(i).gid(g1) == true) {
        clause(i).clear_gid(g1);
        clause(i).set_gid(g2);
      }
    }
  }
  free_gid(g1);
  return g2;
}

void CDatabase::mark_clause_deleted(CClause & cl) {
  ++_stats.num_deleted_clauses;
  _stats.num_deleted_literals += cl.num_lits();
  CLAUSE_STATUS status = cl.status();
  if (status == ORIGINAL_CL)
     _stats.num_del_orig_cls++;
  cl.set_status(DELETED_CL);
  for (unsigned i = 0; i < cl.num_lits(); ++i) {
    CLitPoolElement & l = cl.literal(i);
    --variable(l.var_index()).lits_count(l.var_sign());
    l.val() = 0;
  }
  _unused_clause_idx.insert(&cl - &(*clauses()->begin()));
}

bool CDatabase::is_conflicting(ClauseIdx cl) {
  CLitPoolElement * lits = clause(cl).literals();
  for (int i = 0, sz= clause(cl).num_lits(); i < sz;  ++i) {
    if (literal_value(lits[i]) != 0)
      return false;
  }
  return true;
}

bool CDatabase::is_satisfied(ClauseIdx cl) {
  CLitPoolElement * lits = clause(cl).literals();
  for (int i = 0, sz = clause(cl).num_lits(); i < sz; ++i) {
    if (literal_value(lits[i]) == 1)
      return true;
  }
  return false;
}

bool CDatabase::is_unit(ClauseIdx cl) {
  int num_unassigned = 0;
  CLitPoolElement * lits = clause(cl).literals();
  for (unsigned i = 0, sz= clause(cl).num_lits(); i < sz;  ++i) {
    int value = literal_value(lits[i]);
    if (value == 1)
      return false;
    else if (value != 0)
      ++num_unassigned;
  }
  return num_unassigned == 1;
}

int CDatabase::find_unit_literal(ClauseIdx cl) {
  // will return 0 if not unit
  int unit_lit = 0;
  for (int i = 0, sz = clause(cl).num_lits(); i < sz;  ++i) {
    int value = literal_value(clause(cl).literal(i));
    if (value == 1)
      return 0;
    else if (value != 0) {
      if (unit_lit == 0)
        unit_lit = clause(cl).literals()[i].s_var();
      else
        return 0;
    }
  }
  return unit_lit;
}

inline CLitPoolElement * CDatabase::lit_pool_begin(void) {
  return _lit_pool_start;
}

inline CLitPoolElement * CDatabase::lit_pool_end(void) {
  return _lit_pool_finish;
}

inline void CDatabase::lit_pool_incr_size(int size) {
  _lit_pool_finish += size;
  assert(_lit_pool_finish <= _lit_pool_end_storage);
}

inline void CDatabase::lit_pool_push_back(int value) {
  assert(_lit_pool_finish <= _lit_pool_end_storage);
  _lit_pool_finish->val() = value;
  ++_lit_pool_finish;
}

inline int CDatabase::lit_pool_size(void) {
  return _lit_pool_finish - _lit_pool_start;
}

inline int CDatabase::lit_pool_free_space(void) {
  return _lit_pool_end_storage - _lit_pool_finish;
}

inline double CDatabase::lit_pool_utilization(void) {
    // minus num_clauses() is because of spacing (i.e. clause indices)
  return (double)num_literals() / ((double) (lit_pool_size() - num_clauses())) ;
}

inline CLitPoolElement & CDatabase::lit_pool(int i) {
  return _lit_pool_start[i];
}

void CDatabase::compact_lit_pool(void) {
  unsigned i, sz;
  int new_index = 1;
  // first do the compaction for the lit pool
  for (i = 1, sz = lit_pool_size(); i < sz;  ++i) {
    // begin with 1 because 0 position is always 0
    if (!lit_pool(i).is_literal() && !lit_pool(i-1).is_literal()) {
      continue;
    } else {
      lit_pool(new_index) = lit_pool(i);
      ++new_index;
    }
  }
  _lit_pool_finish = lit_pool_begin() + new_index;
  // update all the pointers to the literals;
  // 1. clean up the watched pointers from variables
  for (i = 1, sz = variables()->size(); i < sz;  ++i) {
    variable(i).watched(0).clear();
    variable(i).watched(1).clear();
  }
  for (i = 1, sz = lit_pool_size(); i < sz;  ++i) {
    CLitPoolElement & lit = lit_pool(i);
    // 2. reinsert the watched pointers
    if (lit.is_literal()) {
      if (lit.is_watched()) {
         int var_idx = lit.var_index();
         int sign = lit.var_sign();
         variable(var_idx).watched(sign).push_back(& lit_pool(i));
       }
    } else {  // lit is not literal
    // 3. update the clauses' first literal pointer
      int cls_idx = lit.get_clause_index();
      clause(cls_idx).first_lit() = &lit_pool(i) - clause(cls_idx).num_lits();
    }
  }
  ++_stats.num_compact;
}

bool CDatabase::enlarge_lit_pool(void) {
  // will return true if successful, otherwise false.
  unsigned i, sz;
  // if memory efficiency < 2/3, we do a compaction
  if (lit_pool_utilization() < 0.67) {
    compact_lit_pool();
    return true;
  }
  // otherwise we have to enlarge it.
  // first, check if memory is running out
  int current_mem = estimate_mem_usage();
  float grow_ratio = 1;
  if (current_mem < _params.mem_limit / 4)
    grow_ratio = 2;
  else if (current_mem < _params.mem_limit /2 )
    grow_ratio = 1.5;
  else if (current_mem < _params.mem_limit * 0.8)
    grow_ratio = 1.2;
  if (grow_ratio < 1.2) {
    if (lit_pool_utilization() < 0.9) {  // still has some garbage
      compact_lit_pool();
      return true;
    }
    else
      return false;
  }
  // second, make room for new lit pool.
  CLitPoolElement * old_start = _lit_pool_start;
  CLitPoolElement * old_finish = _lit_pool_finish;
  int old_size = _lit_pool_end_storage - _lit_pool_start;
  int new_size = (int)(old_size * grow_ratio);
  _lit_pool_start = (CLitPoolElement *) realloc(_lit_pool_start,
                                                sizeof(CLitPoolElement) *
                                                new_size);
  _lit_pool_finish = _lit_pool_start + (old_finish - old_start);
  _lit_pool_end_storage = _lit_pool_start + new_size;

  // update all the pointers
  int displacement = _lit_pool_start - old_start;
  for (i = 0; i < clauses()->size(); ++i) {
    if (clause(i).status() != DELETED_CL)
      clause(i).first_lit() += displacement;
  }
  for (i = 0, sz = variables()->size(); i < sz ;  ++i) {
    CVariable & v = variable(i);
    for (int j = 0; j < 2 ; ++j) {
      int k, sz1;
      vector<CLitPoolElement *> & watched = v.watched(j);
      for (k = 0, sz1 = watched.size(); k < sz1 ; ++k) {
        watched[k] += displacement;
      }
    }
  }
  ++_stats.num_enlarge;
  return true;
}

ClauseIdx CDatabase::get_free_clause_idx(void) {
  ClauseIdx new_cl;
  new_cl = _clauses.size();
  _clauses.resize(new_cl + 1);
  clause(new_cl).set_id(_stats.num_added_clauses);
  return new_cl;
}

ClauseIdx CDatabase::add_clause(int * lits, int n_lits, int gflag) {
  int new_cl;
  // a. do we need to enlarge lits pool?
  while (lit_pool_free_space() <= n_lits + 1) {
    if (enlarge_lit_pool() == false)
      return -1;  // mem out, can't enlarge lit pool, because
      // ClauseIdx can't be -1, so it shows error.
  }
  // b. get a free cl index;
  new_cl = get_free_clause_idx();
  // c. add the clause lits to lits pool
  CClause & cl = clause(new_cl);
  cl.init(lit_pool_end(), n_lits, gflag);
  lit_pool_incr_size(n_lits + 1);
  if (n_lits == 2) {
    ++variable(lits[0]>>1).two_lits_count(lits[0] & 0x1);
    ++variable(lits[1]>>1).two_lits_count(lits[1] & 0x1);
  }
  for (int i = 0; i < n_lits; ++i) {
    int var_idx = lits[i] >> 1;
    assert((unsigned)var_idx < variables()->size());
    int var_sign = lits[i] & 0x1;
    cl.literal(i).set(var_idx, var_sign);
    ++variable(var_idx).lits_count(var_sign);
#ifdef KEEP_LIT_CLAUSES
    variable(var_idx).lit_clause(var_sign).push_back(new_cl);
#endif
  }
  // the element after the last one is the spacing element
  cl.literal(n_lits).set_clause_index(new_cl);
  // d. set the watched pointers
  if (cl.num_lits() > 1) {
    // add the watched literal. note: watched literal must be the last free var
    int max_idx = -1, max_dl = -1;
    int i, sz = cl.num_lits();
    // set the first watched literal
    for (i = 0; i < sz; ++i) {
      int v_idx = cl.literal(i).var_index();
      int v_sign = cl.literal(i).var_sign();
      CVariable & v = variable(v_idx);
      if (literal_value(cl.literal(i)) != 0) {
        v.watched(v_sign).push_back(&cl.literal(i));
        cl.literal(i).set_watch(1);
        break;
      } else {
        if (v.dlevel() > max_dl) {
          max_dl = v.dlevel();
          max_idx = i;
        }
      }
    }
    if (i >= sz) {  // no unassigned literal. so watch literal with max dlevel
      int v_idx = cl.literal(max_idx).var_index();
      int v_sign = cl.literal(max_idx).var_sign();
      variable(v_idx).watched(v_sign).push_back(&cl.literal(max_idx));
      cl.literal(max_idx).set_watch(1);
    }

    // set the second watched literal
    max_idx = -1;
    max_dl = -1;
    for (i = sz-1; i >= 0; --i) {
      if (cl.literal(i).is_watched())
        continue;  // need to watch two different literals
      int v_idx = cl.literal(i).var_index();
      int v_sign = cl.literal(i).var_sign();
      CVariable & v = variable(v_idx);
      if (literal_value(cl.literal(i)) != 0) {
        v.watched(v_sign).push_back(&cl.literal(i));
        cl.literal(i).set_watch(-1);
        break;
      } else {
        if (v.dlevel() > max_dl) {
          max_dl = v.dlevel();
          max_idx = i;
        }
      }
    }
    if (i < 0) {
      int v_idx = cl.literal(max_idx).var_index();
      int v_sign = cl.literal(max_idx).var_sign();
      variable(v_idx).watched(v_sign).push_back(&cl.literal(max_idx));
      cl.literal(max_idx).set_watch(-1);
    }
  }
  // update some statistics
  ++_stats.num_added_clauses;
  _stats.num_added_literals += n_lits;
  return new_cl;
}

void CDatabase::output_lit_pool_stats(void) {
  cout << "Lit_Pool Used " << lit_pool_size() << " Free "
       << lit_pool_free_space()
       << " Total " << lit_pool_size() + lit_pool_free_space()
       << " Num. Cl " << num_clauses() << " Num. Lit " << num_literals()
       << " Efficiency " <<  lit_pool_utilization() << endl;
}

void CDatabase::detail_dump_cl(ClauseIdx cl_idx, ostream & os) {
  os << "CL : " << cl_idx;
  CClause & cl = clause(cl_idx);
  if (cl.status() == DELETED_CL)
    os << "\t\t\t======removed=====";
  char value;
  for (unsigned i = 0; i < cl.num_lits(); ++i) {
    if (literal_value(cl.literal(i)) == 0)
      value = '0';
    else if (literal_value(cl.literal(i)) == 1)
      value = '1';
    else
      value = 'X';
    os << cl.literal(i) << "(" << value << "@"
       << variable(cl.literal(i).var_index()).dlevel()<< ")  ";
  }
  os << endl;
}

void CDatabase::dump(ostream & os) {
  unsigned i;
  os << "Dump Database: " << endl;
  for (i = 0; i < _clauses.size(); ++i)
    detail_dump_cl(i);
  for (i = 1; i < _variables.size(); ++i)
    os << "VID " << i << ":\t" << variable(i);
}
