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
// any trademark, service mark, or the name of Princeton University.
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

#include <cstdlib>
#include <cstring>
#include <sys/time.h>
#include <sys/resource.h>
#include <vector>
#include <set>
#include <iostream>
#include <fstream>
#include <assert.h>

using namespace std;

const int WORD_LEN      = 64000;

const int MEM_LIMIT     = 800000;

const int UNKNOWN       = 2;

int _peak_mem;
bool _dump_core;

double get_cpu_time(void) {
  double res;
  struct rusage usage;
  getrusage(RUSAGE_SELF, &usage);
  res = usage.ru_utime.tv_usec + usage.ru_stime.tv_usec;
  res *= 1e-6;
  res += usage.ru_utime.tv_sec + usage.ru_stime.tv_sec;
  return res;
}

void get_line(ifstream* fs, vector<char>* buf) {
  buf->clear();
  buf->reserve(4096);
  while (!fs->eof()) {
    char ch = fs->get();
    if (ch == '\n' || ch == '\377')
      break;
    if (ch == '\r')
      continue;
    buf->push_back(ch);
  }
  buf->push_back('\0');
  return;
}

int get_token(char * & lp, char * token) {
  char * wp = token;
  while (*lp && ((*lp == ' ') || (*lp == '\t'))) {
    lp++;
  }
  while (*lp && (*lp != ' ') && (*lp != '\t') && (*lp != '\n')) {
    *(wp++) = *(lp++);
  }
  *wp = '\0';                                 // terminate string
  return wp - token;
}

int get_mem_usage(void) {
  FILE * fp;
  char buffer[128];
  char token[128];
  char filename[128];

  int pid = getpid();
  snprintf(filename, sizeof(filename), "/proc/%i/status", pid);
  if ((fp = fopen(filename, "r")) == NULL) {
    cerr << "Can't open Proc file, are you sure you are using Linux?" << endl;
    exit(1);
  }
  while (!feof(fp)) {
    fgets(buffer, 128, fp);
    char * ptr = buffer;
    get_token(ptr, token);
    if (strcmp(token, "VmSize:") == 0) {
      get_token(ptr, token);
      fclose(fp);
      return atoi(token);
    }
  }
  cerr << "Error in get memeory usage" << endl;
  exit(1);
  return 0;
}

int my_a2i(char * str) {
  int result = 0;
  bool neg = false;
  if (str[0] == '-') {
    neg = true;
    ++str;
  }
  else if (str[0] == '+')
    ++str;
  for (unsigned i = 0; i < strlen(str); ++i) {
    int d = str[i] - '0';
    if (d < 0 || d > 9) {
      cerr << "Abort: Unable to change " << str << " into a number " << endl;
      exit(1);
    }
    result = result * 10 + d;
  }
  if (neg)
    result = -result;
  return result;
}

class CClause {
  public:
    vector<int> literals;
    vector<int> resolvents;
    bool is_involved    : 1;
    bool is_built       : 1;
    bool is_needed      : 1;

    CClause(void) {
      is_involved = false;
      is_built = false;
      is_needed = false;
    }
    ~CClause(void) {}
};

class CVariable {
  public:
    short       value;
    short       in_clause_phase         :4;
    bool        is_needed               :1;
    int         antecedent;
    int         num_lits[2];
    int         level;
    CVariable(void) {
      value = UNKNOWN;
      antecedent = -1;
      in_clause_phase = UNKNOWN;
      num_lits[0] = num_lits[1] = 0;
      level = -1;
      is_needed = false;
    }
};

struct cmp_var_level {
  bool operator() (CVariable * v1, CVariable * v2) {
    if (v1->level > v2->level)
      return true;
    else if (v1->level < v2->level)
      return false;
    else if ( (size_t)v1 > (size_t)v2)
      return true;
    return false;
  }
};

class CDatabase {
  private:
    int                 _current_num_clauses;
    int                 _num_init_clauses;
    vector<CVariable>   _variables;
    vector<CClause>     _clauses;
    int                 _conf_id;
    vector<int>         _conf_clause;

  public:
    CDatabase(void) {
      _num_init_clauses = 0;
      _current_num_clauses = 0;
      _conf_id = -1;
    }

    int & num_init_clauses(void) {
      return _num_init_clauses;
    }

    vector<CVariable> & variables(void) {
      return _variables;
    }

    vector<CClause> & clauses(void) {
      return  _clauses;
    }

    void read_cnf(char * filename);
    bool verify(char * filename);
    bool real_verify(void);
    int lit_value(int svar) {
      assert(_variables[svar>>1].value != UNKNOWN);
      return _variables[svar>>1].value ^ (svar & 0x1);
    }
    int add_orig_clause_by_lits(vector<int> lits);
    int add_learned_clause_by_resolvents(vector<int> & resolvents);
    void set_var_number(int nvar);
    void set_init_cls_number(int n) {
      _num_init_clauses = n;
    }
    void construct_learned_clauses(void);
    void recursive_construct_clause(int cl_id);
    void recursive_find_involved(int cl_id);
    int recursive_find_level(int vid);
    void dump(void);
};

void CDatabase::dump(void) {
  cout << "p cnf " << _variables.size() - 1 << " " << _num_init_clauses << endl;
  for (unsigned i = 0; i < _clauses.size(); ++i) {
    for (unsigned j = 0; j < _clauses[i].literals.size(); ++j) {
      int lit = _clauses[i].literals[j];
      cout << ((lit & 0x1) ? "-" : "") << (lit >> 1) << " ";
    }
    cout << "0" << endl;
  }
}

void CDatabase::set_var_number(int nvar) {
  _variables.resize(nvar + 1);
  for (unsigned i = 0; i < _variables.size(); ++i) {
    _variables[i].value = UNKNOWN;
    _variables[i].in_clause_phase = UNKNOWN;
  }
}

void check_mem_out(void) {
  int mem = get_mem_usage();
  if (mem > MEM_LIMIT) {
    cerr << "Mem out" << endl;
    exit(1);
  }
  if (mem > _peak_mem)
    _peak_mem = mem;
}

int CDatabase::add_orig_clause_by_lits(vector<int> lits) {
  static int line_n = 0;
  ++line_n;
  if (lits.size() == 0) {
    cerr << "Empty Clause Encountered " << endl;
    exit(1);
  }
  int cls_id = _clauses.size();
  _clauses.resize(_clauses.size() + 1);
  vector<int> temp_cls;
  for (unsigned i = 0; i < lits.size(); ++i) {
    int vid = lits[i];
    int phase = 0;
    if (vid < 0) {
      vid = - vid;
      phase = 1;
    }
    if (vid == 0 || vid > (int) _variables.size() - 1) {
      cerr << "Variable index out of range " << endl;
      exit(1);
    }
    if (_variables[vid].in_clause_phase == UNKNOWN) {
      _variables[vid].in_clause_phase = phase;
      temp_cls.push_back(vid + vid + phase);
//    _clauses[cls_id].my_literals.push_back(vid + vid + phase);
      ++_variables[vid].num_lits[phase];
    }
    else if (_variables[vid].in_clause_phase != phase) {
      cerr << "clause " << line_n << endl;
      cerr << "A clause contain both literal and its negate " << endl;
      exit(1);
    }
  }
  _clauses[cls_id].literals.resize(temp_cls.size());
  for (unsigned i = 0; i< temp_cls.size(); ++i) {
    _clauses[cls_id].literals[i]= temp_cls[i];
  }
  _clauses[cls_id].is_built = true;
//      _clauses[cls_id].my_is_built = true;
  for (unsigned i = 0; i< lits.size(); ++i) {
    int vid = lits[i];
    if (vid < 0) vid = -vid;
    _variables[vid].in_clause_phase = UNKNOWN;
  }
  ++_current_num_clauses;
  if (_current_num_clauses%10 == 0)
    check_mem_out();
  return cls_id;
}

int CDatabase::add_learned_clause_by_resolvents(vector<int> & resolvents) {
  int cls_id = _clauses.size();
  _clauses.resize(_clauses.size() + 1);
  _clauses[cls_id].resolvents.resize(resolvents.size());
  for (unsigned i = 0; i< resolvents.size(); ++i)
    _clauses[cls_id].resolvents[i] = resolvents[i];
  _clauses[cls_id].is_built = false;
  return cls_id;
}

void CDatabase::read_cnf(char * filename) {
  cout << "Read in original clauses ... ";
  ifstream in_file(filename);
  if (!in_file) {
    cerr << "Can't open input CNF file " << filename << endl;
    exit(1);
  }
  vector<char> buffer;
  vector<int> literals;
  bool header_encountered = false;
  char token[WORD_LEN];
  while (!in_file.eof()) {
    get_line(&in_file, &buffer);
    char * ptr = &(*buffer.begin());
    if (get_token(ptr, token)) {
      if (strcmp(token, "c") == 0)
        continue;
      else if (strcmp(token, "p") == 0) {
        get_token(ptr, token);
        if (strcmp(token, "cnf") != 0) {
          cerr << "Format Error, p cnf NumVar NumCls " << endl;
          exit(1);
        }
        get_token(ptr, token);
        int nvar = my_a2i(token);
        set_var_number(nvar);
        get_token(ptr, token);
        int ncls = my_a2i(token);
        set_init_cls_number(ncls);
        header_encountered = true;
        continue;
      } else {
        int lit = my_a2i(token);
        if (lit != 0) {
          literals.push_back(lit);
        } else {
          add_orig_clause_by_lits(literals);
          literals.clear();
        }
      }
    }
    while (get_token(ptr, token)) {
      int lit = my_a2i(token);
      if (lit != 0) {
        literals.push_back(lit);
      } else {
        add_orig_clause_by_lits(literals);
        literals.clear();
      }
    }
  }
  if (!literals.empty()) {
    cerr << "Trailing numbers without termination " << endl;
    exit(1);
  }
  if (clauses().size() != (unsigned)num_init_clauses())
    cerr << "WARNING : Clause count inconsistant with the header " << endl;
  cout << num_init_clauses() << " Clauses " << endl;
}

void CDatabase::recursive_find_involved(int cl_id) {
  if (_clauses[cl_id].is_involved == true)
    return;
  _clauses[cl_id].is_involved = true;

  recursive_construct_clause(cl_id);

  int num_1 = 0;
  for (unsigned i = 0; i < _clauses[cl_id].literals.size(); ++i) {
    int lit = _clauses[cl_id].literals[i];
    int vid = (lit>>1);
    int sign = (lit & 0x1);
    assert(_variables[vid].value != UNKNOWN);
    if ((_variables[vid].value == 1 && sign == 0) ||
      (_variables[vid].value == 0 && sign == 1)) {
      if (num_1 == 0) {
        ++num_1;
      } else {
        cerr << "Clause " << cl_id << " has more than one value 1 literals "
             << endl;
        exit(1);
      }
    } else {  // literal value 0, so seek its antecedent
      int ante = _variables[vid].antecedent;
      recursive_find_involved(ante);
    }
  }
}

void CDatabase::recursive_construct_clause(int cl_id) {
  CClause & cl = _clauses[cl_id];
  if (cl.is_built == true)
    return;

  assert(cl.resolvents.size() > 1);

  // I have to construct them first because of recursion may
  // mess up with the in_clause_signs.
  for (unsigned i = 0; i < cl.resolvents.size(); ++i) {
    _clauses[cl.resolvents[i]].is_needed = true;
    recursive_construct_clause(cl.resolvents[i]);
  }

//      cout << "Constructing clause " << cl_id << endl;
  vector<int> literals;

  // initialize
  int cl1 = cl.resolvents[0];
  assert(_clauses[cl1].is_built);
  for (unsigned i = 0; i < _clauses[cl1].literals.size(); ++i) {
    int lit = _clauses[cl1].literals[i];
    int vid = (lit >> 0x1);
    int sign = (lit & 0x1);
    assert(_variables[vid].in_clause_phase == UNKNOWN);
    _variables[vid].in_clause_phase = sign;
    literals.push_back(lit);
  }

  for (unsigned i = 1; i < cl.resolvents.size(); ++i) {
    int distance = 0;
    int cl1 = cl.resolvents[i];
    assert(_clauses[cl1].is_built);
    for (unsigned j = 0; j < _clauses[cl1].literals.size(); ++j) {
      int lit = _clauses[cl1].literals[j];
      int vid = (lit >> 0x1);
      int sign = (lit & 0x1);
      if (_variables[vid].in_clause_phase == UNKNOWN) {
        _variables[vid].in_clause_phase = sign;
        literals.push_back(lit);
      }
      else if (_variables[vid].in_clause_phase != sign) {
        // distance 1 literal
        ++distance;
        _variables[vid].in_clause_phase = UNKNOWN;
      }
    }
    if (distance != 1) {
      cerr << "Resolve between two clauses with distance larger than 1" << endl;
      cerr << "The resulting clause is " << cl_id << endl;
      cerr << "Starting clause is " << cl.resolvents[0] << endl;
      cerr << "One of the clause involved is " << cl1 << endl;
      exit(1);
    }
  }
  vector<int> temp_cls;
  for (unsigned i = 0; i < literals.size(); ++i) {
    int lit = literals[i];
    int vid = (lit >> 0x1);
    int sign = (lit & 0x1);
    if (_variables[vid].in_clause_phase == UNKNOWN)
      continue;
    assert(_variables[vid].in_clause_phase == sign);
    _variables[vid].in_clause_phase = UNKNOWN;
    temp_cls.push_back(lit);
  }
  cl.literals.resize(temp_cls.size());
  for (unsigned i = 0; i < temp_cls.size(); ++i)
    cl.literals[i] = temp_cls[i];

//      ::sort(cl.literals.begin(), cl.literals.end());
//      assert(cl.literals.size()== cl.my_literals.size());
//      for (unsigned i=0; i< cl.literals.size(); ++i)
//        assert(cl.literals[i] == cl.my_literals[i]);
  cl.is_built = true;
  ++_current_num_clauses;
  if (_current_num_clauses%10 == 0)
    check_mem_out();
}

int CDatabase::recursive_find_level(int vid) {
  int ante = _variables[vid].antecedent;
  assert(_variables[vid].value != UNKNOWN);
  assert(_variables[vid].antecedent != -1);
  assert(_clauses[ante].is_involved);
  if (_variables[vid].level != -1)
    return _variables[vid].level;
  int level = -1;
  for (unsigned i = 0; i <_clauses[ante].literals.size(); ++i) {
    int v = (_clauses[ante].literals[i] >> 1);
    int s = (_clauses[ante].literals[i] & 0x1);
    if (v == vid) {
      assert(_variables[v].value != s);
      continue;
    } else {
      assert(_variables[v].value == s);
      int l = recursive_find_level(v);
      if (level < l )
        level = l;
    }
  }
  _variables[vid].level = level + 1;
  return level + 1;
}

bool CDatabase::real_verify(void) {
  // 1. If a variable is assigned value at dlevel 0,
  // either it's pure or it has an antecedent
  for (unsigned i = 1; i < _variables.size(); ++i) {
    if (_variables[i].value != UNKNOWN && _variables[i].antecedent == -1) {
      if ((_variables[i].num_lits[0] == 0 && _variables[i].value == 0) ||
        (_variables[i].num_lits[1] == 0 && _variables[i].value == 1)) {
//      cout << "Variable " << i << " is assigned " << _variables[i].value
//      << " because it is pure literal. " << endl;
      } else {
        cerr << "Don't know why variable " << i << " is assigned "
             << _variables[i].value << " for no reasons" << endl;
        exit(1);
      }
    }
  }
  // 2. Construct the final conflicting clause if needed and find all
  // the clauses that are involved in making it conflicting
  cout << "Begin constructing all involved clauses " << endl;
  _clauses[_conf_id].is_needed = true;
  recursive_find_involved(_conf_id);
  int count = 0;
  for (unsigned i = num_init_clauses(); i< _clauses.size(); ++i)
    if (_clauses[i].is_built)
      ++count;
  cout << "Num. Learned Clause:\t\t\t" << _clauses.size() - num_init_clauses()
       << endl
       << "Num. Clause Built:\t\t\t" << count << endl
       << "Constructed all involved clauses " << endl;

  // 2.5. Verify the literals in the CONF clause
  // comments this out if it gives error because you give the wrong
  // CONF clause literals.
  assert(_clauses[_conf_id].is_built);
  assert(_clauses[_conf_id].is_involved);
  bool _found;
  for (unsigned i = 0; i <_conf_clause.size(); ++i) {
    _found = false;
    for (unsigned j = 0; j <_clauses[_conf_id].literals.size(); ++j) {
      if (_conf_clause[i] == _clauses[_conf_id].literals[j]) {
        _found = true;
        break;
      }
    }
    if (!_found) {
      cerr << "The conflict clause in trace can't be verified! " << endl;
      cerr << "Literal " << _conf_clause[i] << " is not found." << endl;
    }
  }
  cout << "Conflict clause verification finished." << endl;

  // 3. Levelize the variables that are decided at dlevel 0
  cout << "Levelize variables...";
  for (unsigned i = 1; i < _variables.size(); ++i) {
    int cl_id = _variables[i].antecedent;
    if (_variables[i].value != UNKNOWN &&  cl_id != -1) {
      if (_clauses[cl_id].is_involved) {
           recursive_find_level(i);
//         int level = recursive_find_level(i);
//         cout << "Var: " << i << " level " << level << endl;
      }
    }
  }
  cout << "finished"<< endl;
  // 4. Can we construct an empty clause?
  cout << "Begin Resolution..." ;
  set<CVariable *, cmp_var_level> clause_lits;
  for (unsigned i = 0; i< _clauses[_conf_id].literals.size(); ++i) {
    assert(lit_value(_clauses[_conf_id].literals[i]) == 0);
    int vid = (_clauses[_conf_id].literals[i] >> 1);
    clause_lits.insert(&_variables[vid]);
  }
  assert(clause_lits.size() == _clauses[_conf_id].literals.size());

  while (!clause_lits.empty()) {
//    for (set<CVariable *, cmp_var_level>::iterator itr = clause_lits.begin();
//         itr != clause_lits.end(); ++itr) {
//      int vid = (*itr) - &_variables[0];
//      cout << vid << "(" << (*itr)->level << ") ";
//    }
//    cout << endl;

    int vid = (*clause_lits.begin() - &_variables[0]);
    int ante = _variables[vid].antecedent;
    if (ante == -1) {
      cerr << "Variable " << vid << " has an NULL antecedent ";
      exit(1);
    }
    _clauses[ante].is_needed = true;
    clause_lits.erase(clause_lits.begin());
    _variables[vid].in_clause_phase = 1;
    CClause & cl = _clauses[ante];
    int distance = 0;
    for (unsigned i = 0; i< cl.literals.size(); ++i) {
      int l = cl.literals[i];
      int v = (l>>1);
      assert(_variables[v].value != UNKNOWN);
      if (lit_value(l) == 1) {
        if (vid != v) {
          cerr << "The antecedent of the variable is not really an antecedent "
               << endl;
          exit(1);
        }
        else
          ++distance;
      }
      else
        clause_lits.insert(&_variables[v]);
    }
    assert(distance == 1);
  }
  cout << " Empty clause generated." << endl;
  cout << "Mem Usage :\t\t\t\t" << get_mem_usage()<< endl;
  int needed_cls_count = 0;
  int needed_var_count = 0;
  for (int i = 0; i < num_init_clauses(); ++i) {
    if (_clauses[i].is_needed == true) {
      ++needed_cls_count;
      for (unsigned j = 0; j < _clauses[i].literals.size(); ++j) {
        int vid = (_clauses[i].literals[j] >> 1);
        if (_variables[vid].is_needed == false) {
          ++needed_var_count;
          _variables[vid].is_needed = true;
        }
      }
    }
  }
  cout << "Original Num. Clauses:\t\t\t" << num_init_clauses() << endl;
  cout << "Needed Clauses to Construct Empty:\t"<< needed_cls_count << endl;
  cout << "Total Variable count:\t\t\t" << _variables.size()-1 << endl;
  cout << "Variables involved in Empty:\t\t" << needed_var_count << endl;

  for (unsigned i = 0; i< _clauses.size(); ++i) {
    if (_clauses[i].is_built)
      assert(_clauses[i].is_needed || i < (unsigned)num_init_clauses());
  }
  if (_dump_core == true) {
    cout << "Unsat Core dumped:\t\t\tunsat_core.cnf" << endl;
    ofstream dump("unsat_core.cnf");
    dump << "c Variables Not Involved: ";
    unsigned int k = 0;
    for (unsigned i = 1; i < _variables.size(); ++i) {
      if (_variables[i].is_needed == false) {
        if (k%20 == 0)
          dump << endl << "c ";
        ++k;
        dump << i << " ";
      }
    }
    dump << endl;
    dump << "p cnf " << _variables.size()-1 << " " << needed_cls_count << endl;
    for (int i = 0; i < num_init_clauses(); ++i) {
      if (_clauses[i].is_needed) {
        dump << "c Original Cls ID: " << i << endl;
        for (unsigned j = 0; j < _clauses[i].literals.size(); ++j) {
          dump << ((_clauses[i].literals[j] & 0x1)?" -":" ")
               << (_clauses[i].literals[j] >> 1);
        }
        dump << " 0" << endl;
      }
    }
  }
  return true;
}

bool CDatabase::verify(char * filename) {
  vector<char> buffer;
  char token[WORD_LEN];

  ifstream in_file(filename);
  if (!in_file) {
    cerr << "Can't open input CNF file " << filename << endl;
    exit(1);
  }

  while (!in_file.eof()) {
    get_line(&in_file, &buffer);
    char * ptr = &(*buffer.begin());
    get_token(ptr, token);
    if (strcmp(token, "CL:") == 0) {
      vector<int> resolvents;

      get_token(ptr, token);
      int cl_id = my_a2i(token);

      get_token(ptr, token);
      assert(strcmp(token, "<=") == 0);

      while (get_token(ptr, token)) {
        int r = my_a2i(token);
        resolvents.push_back(r);
      }
      int c = add_learned_clause_by_resolvents(resolvents);
      assert(c == cl_id);
    }
    else if (strcmp(token, "VAR:") == 0) {
      get_token(ptr, token);
      int vid = my_a2i(token);

      get_token(ptr, token);
      assert(strcmp(token, "L:") == 0);
      get_token(ptr, token);  // skip the level

      get_token(ptr, token);
      assert(strcmp(token, "V:") == 0);
      get_token(ptr, token);
      int value = my_a2i(token);
      assert(value == 1 || value == 0);

      get_token(ptr, token);
      assert(strcmp(token, "A:") == 0);
      get_token(ptr, token);
      int ante = my_a2i(token);

      get_token(ptr, token);
      assert(strcmp(token, "Lits:") == 0);

      _variables[vid].value = value;
      _variables[vid].antecedent = ante;
    }
    else if (strcmp(token, "CONF:") == 0) {
      get_token(ptr, token);
      _conf_id = my_a2i(token);

      get_token(ptr, token);
      assert(strcmp(token, "==") == 0);

      while (get_token(ptr, token)) {
        int lit = my_a2i(token);
        assert(lit > 0);
        assert((lit>>1) < (int)_variables.size());
        _conf_clause.push_back(lit);
      }
    }
  }
  if (_conf_id == -1) {
    cerr << "No final conflicting clause defined " << endl;
    exit(1);
  }
  cout << "Mem Usage After Readin file:\t\t" << get_mem_usage() << endl;
  return real_verify();
}

int main(int argc, char** argv) {
  cout << "ZVerify SAT Solver Verifier" << endl;
  cout << "Copyright Princeton University, 2003-2004. All Right Reseverd."
       << endl;
  if (argc != 3 && argc !=4) {
    cerr << "Usage: " << argv[0] << " CNF_File Dump_File [-core]" << endl
       << "-core: dump the unsat core " << endl;
    cerr << endl;
    exit(1);
  }
  if (argc == 3) {
    _dump_core = false;
  } else {
    assert(argc == 4);
    if (strcmp(argv[3], "-core") != 0) {
      cerr << "Must use -core as the third parameter" << endl;
      exit(1);
    }
    _dump_core = true;
  }
  cout << "COMMAND LINE: ";
  for (int i = 0; i < argc; ++i)
    cout << argv[i] << " ";
  cout << endl;

  _peak_mem = get_mem_usage();
  CDatabase dbase;
  double begin_time = get_cpu_time();
  dbase.read_cnf(argv[1]);
  if (dbase.verify(argv[2]) == true) {
    double end_time = get_cpu_time();
    cout << "CPU Time:\t\t\t\t" << end_time - begin_time << endl;
    cout << "Peak Mem Usage:\t\t\t\t" << _peak_mem << endl;
    cout << "Verification Successful " << endl;
  } else {
    cout << "Failed to verify the result " << endl;
  }
  return 0;
}
