// /*********************************************************************
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
// *********************************************************************/

#ifndef __SAT_HEADER__
#define __SAT_HEADER__

#define SAT_Manager void *

typedef long long long64;  // this is for 32 bit unix machines
// typedef long long64;     // this is for Windows or 64 bit unix machines


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

#ifndef _CLS_STATUS_
#define _CLS_STATUS_
enum CLAUSE_STATUS {
    ORIGINAL_CL,
    CONFLICT_CL,
    DELETED_CL,
};
#endif

#ifndef UNKNOWN
#define UNKNOWN         2
#endif

// /*============================================================
//
// This is the header for using the sat solver. A typical flow is
//
// 1. calling SAT_InitManager to get a new manager. You can pre-set
//    the number of variables upfront, or you can add it later by
//    SAT_AddVariable.
//    Variables are indexed from 1, NOT 0.
//
// 2. add clauses by calling SAT_AddClause. Clause is represented by
//    an array of integers. Each literal is represented by
//    2 * VarIndex + Sign. The Sign is 0 for positive phased literals,
//    and 1 for negative phased literals.
//    For example, a clause (3 -5 11 -4 ) should be represented by
//    { 6, 11, 22, 9 }
//    Note: Each variable can occure no more than once in a clause.
//    if a variable occures in both phase, the clause is automatically
//    satisfied. If more than one occurance with same phase, they
//    should be combined. IT IS YOUR RESPONSIBILITY TO KEEP EACH
//    CLAUSE NON-REDUNDENT, or the solver will not function correctly.
//
// 3. zchaff support incremental SAT solving. Clauses can be added
//    or deleted from the database after each run. To accomplish
//    this, a clause is associated with a "Group ID". Each clause
//    has one Group ID. The group of clauses with the same GID can
//    be deleted from the database by calling SAT_DeleteClauseGroup
//    after each run. You need to call SAT_Reset to reset the state
//    of the solver before begining a new run.
//    As an example, the first 10 clauses are associated with GID 1,
//    We add another 2 clauses with GID 2. After solving this instance
//    with 12 clauses, we may want to delete the last 2 clauses and
//    add another 3 clauses. We call SAT_DeleteClauseGroup with GID
//    2 and add the three clauses (these three clauses can have any
//    GID: either 1 if you don't want to delete them in the future,
//    2 if you want to distinguish them from Group 1). Then you should
//    call SAT_Reset() to reset the state of the solver, and call
//    SAT_Solve() again to solve the new instance (a instance with
//    13 clauses).
//    You should obtain free GID using SAT_AllocClauseGroupID. When
//    you call SAT_DeleteClauseGroup, the gid will be freed and can
//    be re-used when you call SAT_AllocClauseGroupID() again.
//    You can also merge two group of clauses into 1 by calling
//    corresponding functions.
//
// 4. Optionally, you may set the time limit and memory limit for
//    the solver, note: time and memory limits are not exact.
//    Also, you can set other paramenters like clause deletion
//    etc.
//
// 5. You can add hook function to do some extra work after
//    a certain number of decisions (branchings). A hook function
//    should accept input of a manager, and has no return value.
//
// 6. Calling SAT_Solve to solve the problem. it will return the
//    status of the solver.
//
// 7. If the problem is satisfiable, you can call SAT_GetVarAsgnment
//    to get a variable assignment which satisfy the problem.
//
// 8. You can also get some statistics from the solver, such as
//    run time, mem usage, etc.
//
// 9. Release the manager by calling SAT_ReleaseManager.
//
// You need to link the library libsat.a, also, though you can compile
// your C program with c compiler when using this sat solver, you
// still need c++ linker to link the library.
//
// Have fun.
//                         The Chaff Team
//                         (contact zfu@EE.Princeton.EDU
//                         for any questions or suggestions)
//                         2004. 3. 10
// =============================================================*/


// Following are the main functions for the flow.

// init a manager
SAT_Manager SAT_InitManager(void);

// get the version of the solver
char * SAT_Version(SAT_Manager mng);

// release a manager
void SAT_ReleaseManager(SAT_Manager mng);

// set the number of variables.
void SAT_SetNumVariables(SAT_Manager mng,
                         int num_vars);

// add a variable. it will return the new var's index
int SAT_AddVariable(SAT_Manager mng);

// the following functions will allow/disallow the variable to be branched
// user may want to branch only on certain variables (for example, primary
// inputs of a circuit, if the CNF is generated from circuit).
// By default, all variables are branchable, usually, if a variable is
// unbranchable, it's value should be determined by all the branchable variables.
// if that's not the case, then these variables may not get an assigned
// value even if the solver says that the problem is satisfiable.
// Notice, the solver determines if a problem is satisfiable by trying to assign
// all the branchable variables. If all such variables can be assigned values
// without causing conflict, then the instance is reported as satisfiable, even
// if the instance is actually unsatisfiable because of unbranchable
// variables being not dependent on branchable variables.
void SAT_EnableVarBranch(SAT_Manager mng, int vid);

void SAT_DisableVarBranch(SAT_Manager mng, int vid);
// add a clause. a literal is a integer with value 2*V_idx + sign
// gid is the group ID. by default, gid equals 0 . Note: group 0
// clauses can't be deleted.
void SAT_AddClause(SAT_Manager          mng,
                   int *                clause_lits,
                   int                  num_lits,
                   int                  gid = 0);

// delete a clause group and learned clauses depending on them.
void SAT_DeleteClauseGroup(SAT_Manager          mng,
                           int                  gid);

// This will reset the solver so it will not keep the implications made before
void SAT_Reset(SAT_Manager mng);

// merge the clause group gid1 with gid2, return a new group which
// contain both groups.
int SAT_MergeClauseGroup(SAT_Manager    mng,
                         int            gid1,
                         int            gid2);

// Allocate a free clause group id. will be -1 if no more available.
// current implementation allow 32 deletable group IDs ranging from
// 1-32. Group 0 is the permanent group (i.e. can't delete).
int SAT_AllocClauseGroupID(SAT_Manager mng);

// followings are for clause gid manipulation
int SAT_IsSetClauseGroupID(SAT_Manager mng, int cl_idx, int id);
int SAT_SetClauseGroupID(SAT_Manager mng, int cl_idx, int id);
int SAT_ClearClauseGroupID(SAT_Manager mng, int cl_idx, int id);
// clauses belong to volatile group will always be deleted when
// SAT_DeleteClauseGroup is called
int SAT_GetVolatileGroupID(SAT_Manager mng);
// clauses belong to global group will never be deleted
int SAT_GetGlobalGroupID(SAT_Manager mng);


void SAT_SetTimeLimit(SAT_Manager       mng,
                      float             runtime);

// note: memory estimation is very rough, so allow 30% of error
// in both SetMemLimit and EstimateMemUsage. Also, in the run
// time, the memory usage could be temporarily 50% larger than
// the limit (this occours when program reallocate memory because
// of insufficiency in the initial allocation).
void SAT_SetMemLimit(SAT_Manager        mng,
                     int                num_bytes);


int SAT_Solve(SAT_Manager mng);
// enum SAT_StatusT
// Get a variable's assignment. -1 means UNKNOWN or undicided
int SAT_GetVarAsgnment(SAT_Manager      mng,
                       int              v_idx);

// this is used for randomness in decision making
void SAT_SetRandomness(SAT_Manager      mng,
                       int              n);
// if the seed < 0, solver will use the day timer to
// get a "psuedo real random" seed.
void SAT_SetRandSeed(SAT_Manager        mng,
                     int                seed);

// add a hookfunction. This function will be called
// every "interval" of decisions. You can add more than
// one such hook functions. i.e. call SAT_AddHookFun more
// than once.
void SAT_AddHookFun(SAT_Manager         mng,
                    void (*fun)(void *),
                    int                 interval);

// /* =======================================================
// This function is for users who want to customize their own
// decision making strategy.
//
// What you can do is add a hook function with interval of 1,
// that function will be called before every decision. Inside
// this hook function, use SAT_MakeDecision to make decision
// with variable "vid" and "sign". sign = 1 means value of
// the variable be 0.
//
// If there are no free variable left, problem is satisfied,
// call SAT_MakeDecision with vid = 0 && sign = 0 will cause
// solver exit with status "SATISFIABLE".
//
// Here is an example:
//
// void my_own_decision (SAT_Manager mng)
// {
// int n_var = SAT_NumVariables(mng);
// int i;
// for (i=1; i<n_var; ++i) {
//   if (SAT_GetVarAsgnment(mng, i)==UNKNOWN){
//     SAT_MakeDecision(mng, i, 1); //make decision with value 0;
//     break;
//   }
// }
// if (i >= n_var) //every var got an assignment, no free var left
//   SAT_MakeDecision (mng, 0, 0);
// }
// ======================================================== */
void SAT_MakeDecision(SAT_Manager        mng,
                      int                vid,
                      int                sign);

// Following are statistics collecting functions
int SAT_EstimateMemUsage(SAT_Manager mng);
// time elapsed from last call of GetElapsedCPUTime
float SAT_GetElapsedCPUTime(SAT_Manager mng);
// current cpu time
float SAT_GetCurrentCPUTime(SAT_Manager mng);
// time spent on the whole solving process
float SAT_GetCPUTime(SAT_Manager mng);

int SAT_NumLiterals(SAT_Manager mng);

int SAT_NumClauses(SAT_Manager mng);

int SAT_NumVariables(SAT_Manager mng);

int SAT_InitNumLiterals(SAT_Manager mng);

int SAT_InitNumClauses(SAT_Manager mng);

long64 SAT_NumAddedLiterals(SAT_Manager mng);

int SAT_NumAddedClauses(SAT_Manager mng);

int SAT_NumShrinkings(SAT_Manager mng);

int SAT_NumDeletedClauses(SAT_Manager mng);

int SAT_NumDelOrigCls(SAT_Manager mng);

long64 SAT_NumDeletedLiterals(SAT_Manager mng);

int SAT_NumDecisions(SAT_Manager mng);
int SAT_NumDecisionsStackConf(SAT_Manager mng);
int SAT_NumDecisionsVsids(SAT_Manager mng);
int SAT_NumDecisionsShrinking(SAT_Manager mng);


int SAT_Random_Seed(SAT_Manager mng);

long64 SAT_NumImplications(SAT_Manager mng);

int SAT_MaxDLevel(SAT_Manager mng);

float SAT_AverageBubbleMove(SAT_Manager mng);
// Following function will allow you to traverse all the
// clauses and literals. Clause is represented by a index.
// The original clauses' indice are not changed during the
// whole process, while added clauses may get deleted, so
// a certain index may not always represent the same
// clause, also, a index may not always be valid.
int SAT_GetFirstClause(SAT_Manager mng);

// GetClauseType will get the clause's type. it can be
// ORIGINAL_CL, CONFLICT_CL, PROBE_CL
int SAT_GetClauseType(SAT_Manager mng, int cl_idx);

// if there are no more clauses left, return value is -1.
// the organization is like :
// index 0 ... InitNumClauses - 1 are the original clauses
// after that, they are added clauses.
int SAT_GetNextClause(SAT_Manager mng, int cl_idx);

int SAT_GetClauseNumLits(SAT_Manager mng, int cl_idx);

// the lits array should have been pre-allocated enough memory
// to store all the lits of a clause. Use SAT_GetClauseNumLits to find
// out before-hand how much memory is required.
void SAT_GetClauseLits(SAT_Manager mng, int cl_idx,  int * lits);

// Following functions dictate the run time behavior
// Don't mess with them unless you know what you are doing
void SAT_EnableConfClsDeletion(SAT_Manager mng);
void SAT_DisableConfClsDeletion(SAT_Manager mng);
void SAT_SetClsDeletionInterval(SAT_Manager mng, int freq);

void SAT_SetMaxUnrelevance(SAT_Manager mng, int n);
void SAT_SetMinClsLenForDelete(SAT_Manager mng, int n);
void SAT_SetMaxConfClsLenAllowed(SAT_Manager mng, int n);

//  void SAT_AllowMultipleConflicts(SAT_Manager mng);
//  void SAT_AllowMultipleConfCls(SAT_Manager mng);
//  void SAT_SetLitPoolCompactRatio(SAT_Manager mng, float ratio);
//  void SAT_SetLitPoolExpantionRatio(SAT_Manager mng, float ration);

// this function cleans all learned clauses in the database.
// it can be called if you incrementally solving many instances and
// the learned clauses occupy too much memory. By calling
// this function, it essentially equal to a fresh restart, i.e. throw
// away the learned clauses obtained so far.
void SAT_CleanUpDatabase(SAT_Manager mng);

// Followings are functions to facilitate the translation from
// Circuit to a CNF representation. It will automatically generate
// the necessary clauses to represent the gates.
// Note: The input convension are the same as in AddClause,
//      e.g. 2 * Vid + Sign
// NOTE: You need to make sure that the signals (a, b, c, o etc) are
// distinctive. I.e. the two inputs to a AND2 gate are different
// signals. Otherwise, the solver may behave incorrectly. Don't
// add a gate that has signal a and a' as inputs. You should do
// these kinds of special case simplifications by yourself.


void SAT_GenClsAnd2(SAT_Manager         mng,
                    int                 a,
                    int                 b,
                    int                 o,
                    int                 gid = 0);

void SAT_GenClsAndN(SAT_Manager         mng,
                    int *               inputs,
                    int                 num_inputs,
                    int                 o,
                    int                 gid = 0);

void SAT_GenClsOr2(SAT_Manager          mng,
                   int                  a,
                   int                  b,
                   int                  o,
                   int                  gid = 0);

void SAT_GenClsOrN(SAT_Manager          mng,
                   int *                inputs,
                   int                  num_inputs,
                   int                  o,
                   int                  gid = 0);

void SAT_GenClsNand2(SAT_Manager        mng,
                     int                a,
                     int                b,
                     int                o,
                     int                gid = 0);

void SAT_GenClsNandN(SAT_Manager        mng,
                     int *              inputs,
                     int                num_inputs,
                     int                o,
                     int                gid = 0);

void SAT_GenClsNor2(SAT_Manager         mng,
                    int                 a,
                    int                 b,
                    int                 o,
                    int                 gid = 0);

void SAT_GenClsNorN(SAT_Manager         mng,
                   int *                inputs,
                   int                  num_inputs,
                   int                  o,
                   int                  gid = 0);

void SAT_GenClsXor(SAT_Manager          mng,
                   int                  a,
                   int                  b,
                   int                  o,
                   int                  gid = 0);

void SAT_GenClsNot(SAT_Manager          mng,
                   int                  a,
                   int                  o,
                   int                  gid = 0);

#endif
