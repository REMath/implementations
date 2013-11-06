
/**
 *  This is a wrapper for zchaff solver
 *
 */
#ifndef _ZCHAFF_OCAML_WRAPPER_H_
#define _ZCHAFF_OCAML_WRAPPER_H_

#include "SAT_C.h"
#include <caml/mlvalues.h>

#ifdef __cplusplus
extern "C"
{
#endif

value zchaff_InitManager(void);

value zchaff_ReleaseManager(value mng);

value zchaff_SetNumVariables(value mng, value num_vars);

value zchaff_AddVariable(value mng);

value zchaff_EnableVarBranch(value mng, value vid);

value zchaff_DisableVarBranch(value mng, value vid);

value zchaff_AddClause(value mng, value clause_lits, value gid);

value zchaff_DeleteClauseGroup(value mng, value gid);

value zchaff_Reset(value mng);

value zchaff_MergeClauseGroup(value mng, value gid1, value gid2);

value zchaff_AllocClauseGroupID(value mng);

value zchaff_IsSetClauseGroupID(value mng, value cl_idx, value id);

value zchaff_SetClauseGroupID(value mng, value cl_idx, value id);

value zchaff_ClearClauseGroupID(value mng, value cl_idx, value id);

value zchaff_GetVolatileGroupID(value mng);

value zchaff_GetGlobalGroupID(value mng);

value  zchaff_SetTimeLimit(value mng, value runtime);

value  zchaff_SetMemLimit(value mng, value num_bytes);

value zchaff_GetVarAsgnment(value mng, value v_idx);

value zchaff_SetRandSee(value mng, value seed);

value zchaff_EstimateMemUsage(value mng);

value zchaff_GetElapseCPUTime(value mng);

value zchaff_GetCurrentCPUTime(value mng);

value zchaff_GetCurrentCPUTime(value mng);

value zchaff_GetElapsedCPUTime(value mng);

value zchaff_NumLiterals(value mng);

value zchaff_NumClauses(value mng);

value zchaff_NumVariables(value mng);

value zchaff_InitNumLiterals(value mng);

value zchaff_InitNumClauses(value mng);

value zchaff_NumAddedLiterals(value mng);

value zchaff_NumAddedClauses(value mng);

value zchaff_NumDeletedClauses(value mng);

value zchaff_NumDecisions(value mng);

value zchaff_NumImplications(value mng);

value zchaff_MaxDLevel(value mng);

value zchaff_AverageBubbleMove(value mng);

value zchaff_GetFirstClause(value mng);

value zchaff_GetClauseLits(value mng, value cl_idx, value lits);

value zchaff_EnableConfClsDeletion(value mng);

value zchaff_DisableConfClsDelection(value mng);

value zchaff_SetClsDeletionInterval(value mng, value freq);

value zchaff_SetMaxUnrelevance(value mng, value n);

value zchaff_SetMinClsLenForDelete(value mng, value n);

value zchaff_SetMaxConfClsLenAllowed(value mng,value n);

value zchaff_GenClsAnd2(value mng, value a, value b, 
		       value o, value gid);

value zchaff_GenClsAndN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o, 
			 value gid);

value zchaff_GenClsOr2	(value mng, 
			 value a,
			 value b,
			 value o, 
			 value gid );


value zchaff_GenClsOrN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o, 
			 value gid );

value zchaff_GenClsNand2	(value mng, 
			 value a,
			 value b,
			 value o,
			 value gid );

value zchaff_GenClsNandN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o,
			 value gid );

value zchaff_GenClsNor2	(value mng, 
			 value a,
			 value b,
			 value o, 
			 value gid );

value zchaff_GenClsNorN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o,
			 value gid);

value zchaff_GenClsXor	(value mng, 
			 value a,
			 value b,
			 value o,
			 value gid );

value zchaff_GenClsNot	(value mng, 
			 value a,
			 value o,
			 value gid);

#ifdef __cplusplus
}
#endif

#endif

