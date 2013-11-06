
type zchaff_solver 

type zcore_database

type clause = int array

external zchaff_InitManager : unit -> zchaff_solver = "zchaff_InitManager"

external zchaff_ReleaseManager : zchaff_solver -> unit = "zchaff_ReleaseManager"

external zchaff_SetNumVariables : zchaff_solver -> int -> unit = "zchaff_SetNumVariables"

external zchaff_AddVariable : zchaff_solver -> int = "zchaff_AddVariable"

(*
external zchaff_EnableVarBranch : zchaff_solver -> int -> unit = "zchaff_EnableVarBranch"

external zchaff_DisableVarBranch : zchaff_solver -> int -> unit = "zchaff_DisableVarBranch"
*)

external zchaff_AddClause : zchaff_solver -> clause -> int -> unit = "zchaff_AddClause"

external zchaff_DeleteClauseGroup : zchaff_solver -> int -> unit = "zchaff_DeleteClauseGroup"

external zchaff_Reset : zchaff_solver -> unit = "zchaff_Reset"

(*
external zchaff_MergeClauseGroup : zchaff_solver -> int -> int -> int = "zchaff_MergeClauseGroup"
*)

external zchaff_AllocClauseGroupID : zchaff_solver -> int = "zchaff_AllocClauseGroupID"

(*
external zchaff_IsSetClauseGroupID : zchaff_solver -> int -> int -> int = "zchaff_IsSetClauseGroupID"

external zchaff_SetClauseGroupID : zchaff_solver -> int -> int = "zchaff_SetClauseGroupID"

external zchaff_ClearClauseGroupID : zchaff_solver -> int -> int = "zchaff_ClearClauseGroupID"

external zchaff_GetVolatileGroupID : zchaff_solver -> int = "zchaff_GetVolatileGroupID"

external zchaff_GlobalGroupID : zchaff_solver -> int = "zchaff_GetGlobalGroupID"
*)

external zchaff_SetTimeLimit : zchaff_solver -> float -> unit = "zchaff_SetTimeLimit"

(*
external zchaff_SetMemLimit : zchaff_solver -> int -> unit = "zchaff_SetMemLimit"
*)

external zchaff_GetVarAsgnment : zchaff_solver -> int -> int = "zchaff_GetVarAsgnment"

external zchaff_Solve : zchaff_solver -> int = "zchaff_Solve"

(*
external zchaff_SetRandomness : zchaff_solver -> int -> unit = "zchaff_SetRandomness"

external zchaff_SetRandSeed : zchaff_solver -> int -> unit = "zchaff_SetRandSeed"

external zchaff_MakeDecision : zchaff_solver -> int -> int -> unit = "zchaff_MakeDecision"

external zchaff_EstimateMemUsage : zchaff_solver -> int = "zchaff_EstimateMemUsage"

external zchaff_GetElapseCPUTime : zchaff_solver -> float = "zchaff_GetElapseCPUTime"

external zchaff_GetCurrentCPUTime : zchaff_solver -> float = "zchaff_GetCurrentCPUTime"

external zchaff_GetCPUTime: zchaff_solver -> float = "zchaff_GetCPUTime"
*)

external zchaff_NumLiteral : zchaff_solver -> int = "zchaff_NumLiterals"

external zchaff_NumClauses : zchaff_solver -> int = "zchaff_NumClauses"

external zchaff_NumVariables : zchaff_solver -> int = "zchaff_NumVariables"

(*
external zchaff_InitNumLiterals : zchaff_solver -> int64 = "zchaff_InitNumLiterals"

external zchaff_InitNumClauses : zchaff_solver -> int = "zchaff_InitNumClauses"

external zchaff_NumAddedLiterals : zchaff_solver -> int64 = "zchaff_NumAddedLiterals"

external zchaff_NumAddedClauses : zchaff_solver -> int = "zchaff_NumAddedClauses"

external zchaff_NumDeletedClauses : zchaff_solver -> int = "zchaff_NumDeletedClauses"

external zchaff_NumDecisions : zchaff_solver -> int = "zchaff_NumDecisions"

external zchaff_NumImplications : zchaff_solver -> int64 = "zchaff_NumImplications"

external zchaff_MaxDLevel : zchaff_solver -> int = "zchaff_MaxDLevel"

external zchaff_AverageBubbleMove : zchaff_solver -> float = "zchaff_AverageBubbleMove"

external zchaff_GetFirstClause : zchaff_solver -> int = "zchaff_GetFirstClause"
*)

(* This function does not work properly *)

(*
external zchaff_GetClauseLits : zchaff_solver -> int -> int -> unit = "zchaff_GetClauseLits"
*)

(*-----------------------------------*)

(*
external zchaff_EnableConfClsDeletion : zchaff_solver -> unit = "zchaff_EnableConfClsDeletion"

external zchaff_DisableConfClsDeletion : zchaff_solver -> unit = "zchaff_DisableConfClsDeletion"

external zchaff_SetClsDeletionInterval : zchaff_solver -> int -> unit = "zchaff_SetClsDeletionInterval"

external zchaff_SetMaxUnrelevance : zchaff_solver -> int -> unit = "zchaff_SetMaxUnrelevance"

external zchaff_SetMinClsLenForDelete : zchaff_solver -> int -> unit = "zchaff_SetMinClsLenForDelete"

external zchaff_SetMaxConfClsLenAllowed : zchaff_solver -> int -> unit = "zchaff_SetMaxConfClsLenAllowed"
*)

(*********** The following are  Helper functions **************)

(*
external zchaff_ReadCnf : zchaff_solver -> string -> unit = "zchaff_ReadCnf"

external zchaff_HandleResult: zchaff_solver -> int -> string -> unit = "zchaff_HandleResult"

external zchaff_OutputStatus : zchaff_solver -> unit = "zchaff_OutputStatus"

external zchaff_VerifySolution : zchaff_solver -> unit = "zchaff_VerifySolution"
*)


(*
let zchaff_GetVarAssign  (mysolver: zchaff_solver) =
  let sz = zchaff_NumVariables (mysolver) in
  let varArray = Array.make (sz+1) 0 in
  let get_var_val idx = zchaff_GetVarAsgnment (mysolver) idx in
    for i = 1 to sz do
      match get_var_val (i) with
	  -1 -> varArray.(i) <- i
	| 0  -> varArray.(i) <- (-i)
	| 1  -> varArray.(i) <- i
        | _  -> varArray.(i) <- -1
    done;
    varArray
*)



(*********** The following are functions for zcore ***********)

(*

external zcore_InitDatabase : unit -> zcore_database = "zcore_InitDatabase"

external zcore_ReleaseDatabase : zcore_database -> unit = "zcore_ReleaseDatabase"

external zcore_ReadCnf : zcore_database -> string -> unit = "zcore_ReadCnf"

external zcore_ProduceCore : zcore_database -> string -> string -> unit = "zcore_ProduceCore"

external zcore_ProduceCore2 : string -> string -> string -> int -> unit = "zcore_ProduceCore2"
*)



(* The following are functions for circuits convertion 
external zchaff_GenClsAnd2 : zchaff_solver -> int -> int -> int -> int -> unit = "zchaff_GenClsAnd2"

external zchaff_GenClsAndN : zchaff_solver -> int array -> int -> int -> int -> unit = "zchaff_GenClsAndN"
 
*)


(*

void zchaff_GenClsOr2	(value mng, 
			 value a,
			 value b,
			 value o, 
			 value gid )
{
  SAT_GenClsOr2( value_to_ptr(mng), Int_val(a), Int_val(b), 
		 Int_val(o), Int_val(gid) );
}

void zchaff_GenClsOrN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o, 
			 value gid )
{

}

void zchaff_GenClsNand2	(value mng, 
			 value a,
			 value b,
			 value o,
			 value gid )
{

}

void zchaff_GenClsNandN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o,
			 value gid )
{

}

void zchaff_GenClsNor2	(value mng, 
			 value a,
			 value b,
			 value o, 
			 value gid )
{

}

void zchaff_GenClsNorN	(value mng, 
			 value inputs,
			 value num_inputs,
			 value o,
			 value gid)
{

}

void zchaff_GenClsXor	(value mng, 
			 value a,
			 value b,
			 value o,
			 value gid )
{

}

void zchaff_GenClsNot	(value mng, 
			 value a,
			 value o,
			 value gid)
{

}

*)

(*
let zchaff = ref (zchaff_InitManager ())
let global_clause_gid = ref (-1)
let already_fed_all_clauses = ref false
let time_limit = ref 0.

let feed_zchaff_all_clauses _ =
  if !global_clause_gid = -1 then global_clause_gid := zchaff_AllocClauseGroupID !zchaff;
  if not !already_fed_all_clauses then (zchaff_SetNumVariables !zchaff !number_variables;
                                        for i = 0 to !number_clauses-1 do
                                          zchaff_AddClause !zchaff (Array.of_list(!clauses.(i))) !global_clause_gid;
                                        done;
                                        already_fed_all_clauses := true)


let check_for_unsat_val _ =
  feed_zchaff_all_clauses ();
  if !time_limit > 0. then zchaff_SetTimeLimit !zchaff !time_limit;
  let r = zchaff_Solve !zchaff in
  match r with
        1 -> true
      | _ -> false *)
(*      | _ -> failwith "SAT solver reports neither satisfiable nor unsatisfiable" *)

(*
let zchaff_set_time_limit f = (time_limit := f)

*)
