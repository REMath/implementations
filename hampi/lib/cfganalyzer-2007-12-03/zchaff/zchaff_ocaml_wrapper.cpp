
/**
 *  This is a wrapper for zchaff solver
 *
 */

#include "SAT_C.h"
#include "zchaff_solver.h"
#include "zchaff_clsgen.h"
#include "zchaff_ocaml_wrapper.h"
#include <sys/types.h>
#include <dirent.h>
#include <iostream>
#include <fstream>
#include <streambuf>



using namespace std;

void my_read_cnf(SAT_Manager mng, char * filename );
void my_handle_result(SAT_Manager mng, int outcome, char * filename );
void my_output_status(SAT_Manager mng);
void my_verify_solution(SAT_Manager mng);


#ifdef __cplusplus
extern "C" {
#endif

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>

#ifdef __cplusplus
}
#endif

static const int MAX_LINE_LENGTH       = 65536;
static const int MAX_WORD_LENGTH       = 64;


/*
/// helper function
//
//This cnf parser function is based on the GRASP code by Joao Marques Silva
void my_read_cnf(SAT_Manager mng, char * filename )
{
//    cout <<"read cnf "<<endl;
    char line_buffer[MAX_LINE_LENGTH];
    char word_buffer[MAX_WORD_LENGTH];
    set<int> clause_vars;
    set<int> clause_lits;
    int line_num = 0;
    
    if(opendir(filename)){
        cerr << "Can't open input file, it's a directory" << endl;
        exit(1);
    }
    
    ifstream inp (filename, ios::in);
    if (!inp) {
        cerr << "Can't open input file" << endl;
        exit(1);
    }
    while (inp.getline(line_buffer, MAX_LINE_LENGTH)) {
        ++ line_num;
        if (line_buffer[0] == 'c') { 
            continue; 
        }
        else if (line_buffer[0] == 'p') {
            int var_num;
            int cl_num;

            int arg = sscanf (line_buffer, "p cnf %d %d", &var_num, &cl_num);
            if( arg < 2 ) {
                cerr << "Unable to read number of variables and clauses"
                     << "at line " << line_num << endl;
                exit(3);
            }
            SAT_SetNumVariables(mng, var_num); //first element not used.
        }
        else {                             // Clause definition or continuation
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
                    int var_idx = atoi (word_buffer);
                    int sign = 0;

                    if( var_idx != 0) {
                        if( var_idx < 0)  { var_idx = -var_idx; sign = 1; }
                        clause_vars.insert(var_idx);
                        clause_lits.insert( (var_idx << 1) + sign);
                    }         
                    else {
                        //add this clause
                        if (clause_vars.size() != 0 && (clause_vars.size() == clause_lits.size())) { //yeah, can add this clause
                            vector <int> temp;
                            for (set<int>::iterator itr = clause_lits.begin();
                                 itr != clause_lits.end(); ++itr)
                                temp.push_back (*itr);
                            SAT_AddClause(mng, & temp.begin()[0], temp.size(), 0);
                        }
                        else {} //it contain var of both polarity, so is automatically satisfied, just skip it
                        clause_lits.clear();
                        clause_vars.clear();
                    }
                }
            }
            while (*lp);
        }
    }
    if (!inp.eof()) {
        cerr << "Input line " << line_num <<  " too long. Unable to continue..." << endl;
        exit(2);
    }
//    assert (clause_vars.size() == 0);         //some benchmark has no 0 in the last clause
    if (clause_lits.size() && clause_vars.size()==clause_lits.size() ) {
        vector <int> temp;
        for (set<int>::iterator itr = clause_lits.begin();
             itr != clause_lits.end(); ++itr)
            temp.push_back (*itr);
        SAT_AddClause(mng, & temp.begin()[0], temp.size(), 0 );
    }
    clause_lits.clear();
    clause_vars.clear();
//    cout <<"done read cnf"<<endl;
}
*/

/*
class nullbuf: std::streambuf {
      static int const bufsize = 1024; // random value!
    public:
      nullbuf() { setp(buffer, buffer + bufsize); }
    protected:
      int_type overflow(int_type c) {
        setp(buffer, buffer + bufsize); // empty the buffer
        return traits_type::not_eof(c); // signal success
      }
    private:
      char buffer[bufsize];
    };
*/

/*

void my_handle_result(SAT_Manager mng, int outcome, char * filename )
{
    char * result = "UNKNOWN";
    switch (outcome) {
    case SATISFIABLE:
        cout << "Instance Satisfiable" << endl;
//following lines will print out a solution if a solution exist
        for (int i=1, sz = SAT_NumVariables(mng); i<= sz; ++i) {
            switch(SAT_GetVarAsgnment(mng, i)) {
            case -1:        
                cout <<"("<< i<<")"; break;
            case 0:
                cout << "-" << i; break;
            case 1:
                cout << i ; break;
            default:
                cerr << "Unknown variable value state"<< endl;
                exit(4);
            }
            cout << " ";
        }
        result  = "SAT";
        break;
    case UNSATISFIABLE:
        result  = "UNSAT";
        cout << "Instance Unsatisfiable" << endl;
        break; 
    case TIME_OUT:
        result  = "ABORT : TIME OUT"; 
        cout << "Time out, unable to determine the satisfiability of the instance"<<endl;
        break;
    case MEM_OUT:
        result  = "ABORT : MEM OUT"; 
        cout << "Memory out, unable to determine the satisfiability of the instance"<<endl;
        break;
    default:
        cerr << "Unknown outcome" << endl;
    }
    cout << "Random Seed Used\t\t\t\t" << SAT_Random_Seed(mng) << endl;
    cout << "Max Decision Level\t\t\t\t" << SAT_MaxDLevel(mng) << endl;
    cout << "Num. of Decisions\t\t\t\t" << SAT_NumDecisions(mng)<< endl;
    cout << "( Stack + Vsids + Shrinking Decisions )\t\t" <<SAT_NumDecisionsStackConf(mng);
    cout << " + " <<SAT_NumDecisionsVsids(mng)<<" + "<<SAT_NumDecisionsShrinking(mng)<<endl;
    cout << "Original Num Variables\t\t\t\t" << SAT_NumVariables(mng) << endl;
    cout << "Original Num Clauses\t\t\t\t" << SAT_InitNumClauses(mng) << endl;
    cout << "Original Num Literals\t\t\t\t" << SAT_InitNumLiterals(mng) << endl;
    cout << "Added Conflict Clauses\t\t\t\t" << SAT_NumAddedClauses(mng)- SAT_InitNumClauses(mng)<< endl;
    cout << "Num of Shrinkings\t\t\t\t" << SAT_NumShrinkings(mng)<< endl;
    cout << "Deleted Conflict Clauses\t\t\t" << SAT_NumDeletedClauses(mng)-SAT_NumDelOrigCls(mng) <<endl;
    cout << "Deleted Clauses\t\t\t\t\t" << SAT_NumDeletedClauses(mng) <<endl;
    cout << "Added Conflict Literals\t\t\t\t" << SAT_NumAddedLiterals(mng) - SAT_InitNumLiterals(mng) << endl;
    cout << "Deleted (Total) Literals\t\t\t" << SAT_NumDeletedLiterals(mng) <<endl;
    cout << "Number of Implication\t\t\t\t" << SAT_NumImplications(mng)<< endl;
    //other statistics comes here
    cout << "Total Run Time\t\t\t\t\t" << SAT_GetCPUTime(mng) << endl;
//    cout << "RESULT:\t" << filename << " " << result << " RunTime: " << SAT_GetCPUTime(mng)<< endl;
    cout  << "RESULT:\t"<<result << endl;


}

void my_output_status(SAT_Manager mng)
{
    cout << "Dec: " << SAT_NumDecisions(mng)<< "\t ";
    cout << "AddCl: " << SAT_NumAddedClauses(mng) <<"\t";
    cout << "AddLit: " << SAT_NumAddedLiterals(mng)<<"\t";
    cout << "DelCl: " << SAT_NumDeletedClauses(mng) <<"\t";
    cout << "DelLit: " << SAT_NumDeletedLiterals(mng)<<"\t";
    cout << "NumImp: " << SAT_NumImplications(mng) <<"\t";
    cout << "AveBubbleMove: " << SAT_AverageBubbleMove(mng) <<"\t";
    //other statistics comes here
    cout << "RunTime:" << SAT_GetElapsedCPUTime(mng) << endl;
}

void my_verify_solution(SAT_Manager mng)
{
    int num_verified = 0;
    for ( int cl_idx = SAT_GetFirstClause (mng); cl_idx >= 0; 
          cl_idx = SAT_GetNextClause(mng, cl_idx)) {
        int len = SAT_GetClauseNumLits(mng, cl_idx);
        int * lits = new int[len+1];
        SAT_GetClauseLits( mng, cl_idx, lits);
        int i;
        for (i=0; i< len; ++i) {
            int v_idx = lits[i] >> 1;
            int sign = lits[i] & 0x1;
            int var_value = SAT_GetVarAsgnment( mng, v_idx);
            if( (var_value == 1 && sign == 0) ||
                (var_value == 0 && sign == 1) ) break;
        }
        if (i >= len) {
            cerr << "Verify Satisfiable solution failed, please file a bug report, thanks. " << endl;
            exit(6);
        }
        delete [] lits;
        ++ num_verified;
    }
    cout <<"c "<< num_verified << " Clauses are true, Verify Solution successful."<<endl;;
}

*/



static inline value ptr_to_value(void* ptr)
{
  value val = alloc(1, Custom_tag);
  Int32_val(val) = (size_t) ptr;
  
  CAMLparam1(val);  

  return val;
}

static inline void* value_to_ptr(value val)
{
  return (void*)Int32_val(val);
}




extern "C" value zchaff_InitManager(void)
{
  CAMLparam0 ();
  SAT_Manager temp = SAT_InitManager();
  CAMLreturn( (value)temp ); 
}


extern "C" value zchaff_ReleaseManager(value mng)
{
  CAMLparam1( mng );
  SAT_Manager solver = (SAT_Manager)mng;
  SAT_ReleaseManager(solver);

  //  printf("zchaff solve is released \n");
  
  // fflush (stdout);

  CAMLreturn(Val_unit);
}

extern "C" value zchaff_SetNumVariables(value mng, value num_vars)
{
  CAMLparam2 ( mng, num_vars );
  SAT_Manager solver = (SAT_Manager)mng;
  SAT_SetNumVariables( solver, Int_val(num_vars));
  CAMLreturn ( Val_unit );
}

extern "C" value zchaff_AddVariable(value mng)
{
  CAMLparam1( mng );
  SAT_Manager solver = (SAT_Manager)mng;
  assert(solver != NULL);
  int retval = SAT_AddVariable(solver);
  CAMLreturn ( Val_int(retval) );
}


/*
extern "C" value zchaff_EnableVarBranch(value mng, value vid)
{
  CAMLparam2 ( mng, vid );
  SAT_Manager solver = (SAT_Manager)mng;
  SAT_EnableVarBranch( solver, Int_val(vid) );
  CAMLreturn( Val_unit );
}

extern "C" value zchaff_DisableVarBranch(value mng, value vid)
{
  CAMLparam2 ( mng, vid );
  SAT_DisableVarBranch( (SAT_Manager)mng, Int_val(vid) );
  CAMLreturn ( Val_unit );
}
*/


extern "C" value zchaff_AddClause(value mng, value clause_lits, value gid)
{
  CAMLparam3 ( mng, clause_lits, gid );
  SAT_Manager solver = (SAT_Manager)mng;

  int size = Wosize_val(clause_lits);
  int * arr = new int[size];
  int i , temp ;
  for (i = 0; i < size; i++)
  {
    temp = Int_val( Field(clause_lits, i) );
    if (temp > 0) 
      arr[i] = temp << 1;
    else
      arr[i] = temp * (-2) + 1;
    
    //    printf("arr[%d]=%d\n", i, arr[i]);
  }

  SAT_AddClause( solver, arr, size, Int_val(gid) );
  CAMLreturn ( Val_unit );
}


extern "C" value zchaff_DeleteClauseGroup(value mng, value gid)
{
  CAMLparam2 ( mng, gid );
  SAT_DeleteClauseGroup( (SAT_Manager)mng, Int_val(gid) );
  CAMLreturn ( Val_unit );
}


extern "C" value  zchaff_Reset(value mng)
{
  CAMLparam1 ( mng );
  SAT_Reset( (SAT_Manager)mng );
  CAMLreturn ( Val_unit );
}


/*
extern "C" value zchaff_MergeClauseGroup(value mng, value gid1, value gid2)
{
  CAMLparam3 ( mng, gid1, gid2 );
  int retval = SAT_MergeClauseGroup( (SAT_Manager) mng, 
				     Int_val(gid1), 
				     Int_val(gid2) );
  CAMLreturn( Val_int(retval) );
}
*/


extern "C" value zchaff_AllocClauseGroupID(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_AllocClauseGroupID( (SAT_Manager)mng );
  CAMLreturn( Val_int( retval ) );
}


/*
extern "C"  value zchaff_IsSetClauseGroupID(value mng, value cl_idx, value id)
{
  CAMLparam3 ( mng, cl_idx, id );
  SAT_Manager solver = value_to_ptr (mng);
  int retval = SAT_IsSetClauseGroupID( solver, Int_val(cl_idx), Int_val(id) );
  CAMLreturn ( Val_int(retval) );
}

extern "C" value zchaff_SetClauseGroupID(value mng, value cl_idx, value id)
{
  CAMLparam3 ( mng, cl_idx, id );
  SAT_Manager solver = (SAT_Manager) mng;
  int retval = SAT_SetClauseGroupID(solver, Int_val(cl_idx), Int_val(id) );
  CAMLreturn ( Val_int(retval) );
}

extern "C" value zchaff_ClearClauseGroupID(value mng, value cl_idx, value id)
{
  CAMLparam3 ( mng, cl_idx, id );
  SAT_Manager solver = (SAT_Manager) mng ;
  int retval = SAT_ClearClauseGroupID(solver, Int_val(cl_idx), Int_val(id));
  CAMLreturn ( Val_int( retval ) );
}

extern "C" value zchaff_GetVolatileGroupID(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_GetVolatileGroupID( (SAT_Manager) mng );
  CAMLreturn ( Val_int( retval ) );
}

extern "C" value zchaff_GetGlobalGroupID(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_GetGlobalGroupID( (SAT_Manager)mng );
  CAMLreturn ( Val_int( retval ) );
}
*/



extern "C" value zchaff_SetTimeLimit(value mng, value runtime)
{
  CAMLparam2 ( mng , runtime );
  SAT_SetTimeLimit( (SAT_Manager)mng, Double_val(runtime) );
  CAMLreturn ( Val_unit );
}


/*
extern "C" value zchaff_SetMemLimit(value mng, value num_bytes)
{
  CAMLparam2 ( mng, num_bytes );
  SAT_SetMemLimit( (SAT_Manager)mng, Int_val(num_bytes) );
  CAMLreturn ( Val_unit );
}
*/


extern "C" value zchaff_Solve( value mng)
{
  cout.setstate(std::ios_base::badbit);

  CAMLparam1 ( mng );
  int retval = SAT_Solve( (SAT_Manager) mng );
  CAMLreturn ( Val_int(retval) );
}

extern "C" value zchaff_GetVarAsgnment(value mng, value v_idx)
{
  CAMLparam2 ( mng, v_idx );
  int retval = SAT_GetVarAsgnment( (SAT_Manager)mng, Int_val(v_idx) );
  CAMLreturn( Val_int(retval) );
}


/*
extern "C" value zchaff_SetRandomness(value mng, value n)
{
  CAMLparam2 ( mng, n );
  SAT_SetRandomness( (SAT_Manager)mng, Int_val(n) );
  CAMLreturn ( Val_unit );
}

extern "C" value zchaff_SetRandSeed(value mng, value seed)
{
  CAMLparam2 ( mng, seed );
  SAT_SetRandSeed( (SAT_Manager)mng, Int_val(seed) );
  CAMLreturn ( Val_unit );
}

extern "C" value zchaff_MakeDecision(value mng, value vid, value sign)
{
  CAMLparam3( mng, vid, sign );
  SAT_MakeDecision( (SAT_Manager)mng, Int_val(vid), Int_val(sign) );
  CAMLreturn ( Val_unit );
}

extern "C" value zchaff_EstimateMemUsage(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_EstimateMemUsage( (SAT_Manager)mng );
  CAMLreturn ( Val_int( retval ) );
}

extern "C" value zchaff_GetElapseCPUTime(value mng)
{
  CAMLparam1 ( mng );
  float val = SAT_GetElapsedCPUTime( (SAT_Manager)mng );
  value res = alloc(1, Double_tag);
  Double_val(res) = val;
  CAMLreturn ( res );
}

extern "C" value zchaff_GetCurrentCPUTime(value mng)
{
  CAMLparam1 ( mng );
  float val = SAT_GetCurrentCPUTime( (SAT_Manager)mng );
  value res = alloc(1, Double_tag);
  Double_val(res) = val;
  CAMLreturn ( res );
}

extern "C" value zchaff_GetCPUTime(value mng) 
{
  CAMLparam1 ( mng );
  float val = SAT_GetCPUTime( value_to_ptr(mng) );
  value res = alloc(1, Double_tag);
  Double_val(res) = val;
  CAMLreturn ( res );
}
*/

extern "C" value zchaff_NumLiterals(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_NumLiterals( (SAT_Manager)mng );
  CAMLreturn ( Val_int(retval) );
}


extern "C" value zchaff_NumClauses(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_NumClauses( (SAT_Manager)mng );
  CAMLreturn ( Val_int(retval) );
}


extern "C" value zchaff_NumVariables(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_NumVariables( (SAT_Manager)mng );
  CAMLreturn ( Val_int(retval) );
}

/*
extern "C" value zchaff_InitNumLiterals(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_InitNumLiterals( (SAT_Manager)mng );
  CAMLreturn ( Val_int(retval) );
}

extern "C" value zchaff_InitNumClauses(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_InitNumClauses( (SAT_Manager)mng );
  CAMLreturn ( Val_int(retval) );
}

extern "C" value zchaff_NumAddedLiterals(value mng)
{
  CAMLparam1 ( mng );
  long64 retval = SAT_InitNumClauses( (SAT_Manager)mng );
  value res = copy_int64 (retval);
  CAMLreturn ( res );
}

extern "C" value zchaff_NumAddedClauses(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_NumAddedClauses( (SAT_Manager)mng );
  CAMLreturn ( Val_int(retval)  );
}

extern "C" value zchaff_NumDeletedClauses(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_NumDeletedClauses( (SAT_Manager)mng );
  CAMLreturn ( Val_int( retval ) );
}

extern "C" value zchaff_NumDecisions(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_NumDecisions( (SAT_Manager)mng );
  CAMLreturn ( Val_int(retval) );
}

extern "C" value zchaff_NumImplications(value mng)
{
  CAMLparam1 ( mng );
  long64 retval = SAT_NumImplications( (SAT_Manager)mng );
  value res = copy_int64( retval );
  Int64_val(res) = retval;
  CAMLreturn ( res );
}

extern "C" value zchaff_MaxDLevel(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_MaxDLevel( (SAT_Manager)mng );
  CAMLreturn ( Val_int(retval) );
}

extern "C" value zchaff_AverageBubbleMove(value mng)
{
  CAMLparam1 ( mng );
  float retval = SAT_AverageBubbleMove( value_to_ptr(mng) );
  value res = alloc(16, Double_tag);
  Double_val(res) = retval;
  CAMLreturn ( res );
}

extern "C" value zchaff_GetFirstClause(value mng)
{
  CAMLparam1 ( mng );
  int retval = SAT_GetFirstClause( (SAT_Manager)mng );
  CAMLreturn ( Val_int(retval) );
}

extern "C" value zchaff_GetClauseLits(value mng, value cl_idx, value lits)
{
  CAMLparam3 ( mng, cl_idx, lits );
  // /*
  SAT_GetClauseLits( value_to_ptr(mng), 
		     Int_val(cl_idx),
		     Int_val(lits) );
  //
  CAMLreturn ( Val_unit );
}

extern "C" value zchaff_EnableConfClsDeletion(value mng)
{
  CAMLparam1 ( mng );
  SAT_EnableConfClsDeletion( (SAT_Manager)mng );
  CAMLreturn ( Val_unit );
}

extern "C" value zchaff_DisableConfClsDeletion(value mng)
{
  CAMLparam1 ( mng );
  SAT_DisableConfClsDeletion( (SAT_Manager)mng );
  CAMLreturn ( Val_unit );
}

*/

// extern "C" value zchaff_SetClsDeletionInterval(value mng, value freq)
// {
//   CAMLparam2 ( mng, freq );
//   SAT_SetClsDeletionInterval( (SAT_Manager)mng, Int_val(freq) );
//   CAMLreturn ( Val_unit );
// }

// extern "C" value zchaff_SetMaxUnrelevance(value mng, value n)
// {
//   CAMLparam2 ( mng, n );
//   SAT_SetMaxUnrelevance( (SAT_Manager)mng, Int_val(n) );
//   CAMLreturn ( Val_unit );
// }

// extern "C" value zchaff_SetMinClsLenForDelete(value mng, value n)
// {
//   CAMLparam2 ( mng, n );
//   SAT_SetMinClsLenForDelete( (SAT_Manager)mng, Int_val(n) );
//   CAMLreturn ( Val_unit );
// }

// extern "C" value zchaff_SetMaxConfClsLenAllowed(value mng,value n)
// {
//   CAMLparam2 ( mng, n );
//   SAT_SetMaxConfClsLenAllowed( (SAT_Manager)mng, Int_val(n) );
//   CAMLreturn ( Val_unit );
// }


/*
extern "C" value zchaff_ReadCnf(value mng, value filename)
{
  CAMLparam2(mng, filename);
  SAT_Manager solver = (SAT_Manager) mng ;

  assert(solver != NULL);
  char * fn = String_val(filename);
  
  my_read_cnf(solver, fn);
  CAMLreturn ( Val_unit );
}

extern "C" value  zchaff_HandleResult(value mng, value outcome, value filename)
{
  CAMLparam3 ( mng, outcome, filename );
  my_handle_result( (SAT_Manager)mng, 
		 Int_val(outcome),
		 String_val(filename) );
  CAMLreturn ( Val_unit );
}

extern "C" value zchaff_OutputStatus(value mng)
{
  CAMLparam1 ( mng );
  my_output_status( (SAT_Manager)mng );
  CAMLreturn ( Val_unit );
}

extern "C" value zchaff_VerifySolution(value mng)
{
  CAMLparam1 ( mng );
  my_verify_solution( (SAT_Manager)mng );
  CAMLreturn ( Val_unit );
}


*/

/*****************
 * 
 *  The following are wrapper functions for helper functions
 *  These functions are declared in 
 *  ../include/zchaff_solver_helper.h
 *
 */


/*
void zchaff_GenClsAnd2(value mng, value a, value b, 
		       value o, value gid)
{

}


void zchaff_GenClsAndN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o, 
			 value gid)
{
  
}

void zchaff_GenClsOr2	(value mng, 
			 value a,
			 value b,
			 value o, 
			 value gid )
{

}

void zchaff_GenClsOrN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o, 
			 value gid )
{

}

value zchaff_GenClsNand2(value mng, 
			 value a,
			 value b,
			 value o,
			 value gid )
{
  CAMLreturn ( Val_unit );
}

value zchaff_GenClsNandN(value mng, 
			 value inputs,
			 value num_inputs,
			 value o,
			 value gid )
{
  CAMLreturn ( Val_unit );
}

value zchaff_GenClsNor2	(value mng, 
			 value a,
			 value b,
			 value o, 
			 value gid )
{
  CAMLreturn ( Val_unit );
}

value zchaff_GenClsNorN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o,
			 value gid)
{
  CAMLreturn ( Val_unit );
}

value zchaff_GenClsXor	(value mng, 
			 value a,
			 value b,
			 value o,
			 value gid )
{
  CAMLreturn ( Val_unit );
}

value zchaff_GenClsNot	(value mng, 
			 value a,
			 value o,
			 value gid)
{
  CAMLreturn ( Val_unit );
}

//*/

