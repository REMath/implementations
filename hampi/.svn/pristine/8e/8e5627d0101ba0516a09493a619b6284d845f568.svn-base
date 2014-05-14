#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstdio>
#include <cstring>


#include <set>
#include <vector>
#include <assert.h>

using namespace std;

const int MAX_WORD_LENGTH       = 64;
const int MAX_LINE_LENGTH       = 256000;

int main(int argc, char** argv) {
  assert(argc == 2);
  char * filename = argv[1];
  int line_num = 0;
  char line_buffer[MAX_LINE_LENGTH];
  char word_buffer[MAX_WORD_LENGTH];
  set<int> clause_vars;
  set<int> clause_lits;
  int num_cls = 0;
  vector<bool> variables;
  int var_num;
  int cl_num;
  ifstream inp(filename, ios::in);
  if (!inp) {
    cerr << "Can't open input file" << endl;
    exit(1);
  }
  while (inp.getline(line_buffer, MAX_LINE_LENGTH)) {
    ++line_num;
    if (line_buffer[0] == 'c') {
      continue;
    }
    else if (line_buffer[0] == 'p') {
      int arg = sscanf(line_buffer, "p cnf %d %d", &var_num, &cl_num);
      if (arg < 2) {
        cerr << "Unable to read number of variables and clauses"
             << "at line " << line_num << endl;
        exit(3);
      }
      variables.resize(var_num + 1);
      for (int i = 0; i < var_num + 1; ++i)
        variables[i] = false;
    } else {                             // Clause definition or continuation
      char *lp = line_buffer;
      do {
        char *wp = word_buffer;
        while (*lp && ((*lp == ' ') || (*lp == '\t'))) {
          lp++;
        }
        while (*lp && (*lp != ' ') && (*lp != '\t') && (*lp != '\n')) {
          *(wp++) = *(lp++);
        }
        *wp = '\0';                                 // terminate string

        if (strlen(word_buffer) != 0) {     // check if number is there
          int var_idx = atoi(word_buffer);
          int sign = 0;

          if (var_idx != 0) {
            if (var_idx < 0) {
              var_idx = -var_idx;
              sign = 1;
            }
            clause_vars.insert(var_idx);
            clause_lits.insert((var_idx << 1) + sign);
          } else {
            // add this clause
            if (clause_vars.size() != 0 &&
                clause_vars.size() == clause_lits.size()) {
              vector <int> temp;
              for (set<int>::iterator itr = clause_lits.begin();
                itr != clause_lits.end(); ++itr)
                temp.push_back(*itr);
              for (unsigned i = 0; i < temp.size(); ++i)
                variables[temp[i]>>1] = true;
              ++num_cls;
            } else {
              cout << "Literals of both polarity at line "
                   << line_num << ", clause skipped " << endl;
            }
            // it contain var of both polarity, so is automatically
            // satisfied, just skip it
            clause_lits.clear();
            clause_vars.clear();
          }
        }
      }
      while (*lp);
    }
  }
  if (!inp.eof()) {
    cerr << "Input line " << line_num <<  " too long. Unable to continue..."
         << endl;
    exit(2);
  }
  assert(clause_vars.size() == 0);
  int num_vars  = 0;
  for (unsigned i = 0; i < variables.size(); ++i) {
    if (variables[i])
      ++num_vars;
  }
  cout <<"Statistics of CNF file:\t\t" <<  filename << "\n"
     <<" Claim:\t\t Cl: " << cl_num << "\t Var: " << var_num << "\n"
     <<" Actual:\t Cl: " << num_cls << "\t Var: " << num_vars << endl;
  return 0;
}
