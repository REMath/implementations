open Basics ;;
open Problems ;;
open Zchaff ;;

let bound_reached = ref false
let time_limit_reached = ref false
let time_out = ref (-1.0)
let maximum_bound = ref (-1)
 
let showClause c =
  let c = Array.to_list c in
  "[" ^ String.concat "," (List.map string_of_int c) ^ "]"

let engine problem =
  let permanentClauseGID = zchaff_AllocClauseGroupID zchaff in
  let time = Sys.time () in

  let rec run_engine lower_k upper_k =
    if !maximum_bound > 0 && lower_k >= !maximum_bound 
    then (message 2 (fun _ -> "Search terminated because maximal bound of " ^ string_of_int !maximum_bound ^ 
                             " has been reached.\n");
          bound_reached := true)
    else if !time_out >= 0.0 && Sys.time () -. time > !time_out 
    then (message 2 (fun _ -> "Search terminated after time out occurred.\n");
          time_limit_reached := true)
    else (
    message 2 (fun _ -> "Now testing length range [" ^ string_of_int (lower_k + 1) ^ ".." ^ 
                        string_of_int (upper_k + 1) ^ "].\n");
    message 2 (fun _ -> "  Creating permanent constraints ... "); 
    let t = Sys.time () in
    List.iter
      (fun cm -> let constraints = cm lower_k upper_k in
                 List.iter
                   (fun c -> message 3 (fun _ -> "  Adding clause " ^ showClause c ^ "\n");
                             zchaff_AddClause zchaff c permanentClauseGID)
                   constraints)
      problem.permanent;
    message 2 (fun _ -> Printf.sprintf "%.2f" (Sys.time () -. t) ^ "sec\n"); 
    message 2 (fun _ -> "  Currently " ^ string_of_int (zchaff_NumClauses zchaff) ^ " clauses, " ^ 
                        string_of_int (zchaff_NumLiteral zchaff) ^ " literals, " ^ 
                        string_of_int (zchaff_NumVariables zchaff) ^ " variables.\n"); 
    let temporaryClauseGID = zchaff_AllocClauseGroupID zchaff in
    message 2 (fun _ -> "  Creating temporary constraints ... "); 
    let t = Sys.time () in
    List.iter
      (fun cm -> let constraints = cm lower_k upper_k in
                 List.iter
                   (fun c -> message 3 (fun _ -> "  Adding clause " ^ showClause c ^ "\n");
                             zchaff_AddClause zchaff c temporaryClauseGID)
                   constraints)
      problem.temporary;
    message 2 (fun _ -> Printf.sprintf "%.2f" (Sys.time () -. t) ^ "sec\n"); 
    message 2 (fun _ -> "  Currently " ^ string_of_int (zchaff_NumClauses zchaff) ^ " clauses, " ^ 
                        string_of_int (zchaff_NumLiteral zchaff) ^ " literals, " ^ 
                        string_of_int (zchaff_NumVariables zchaff) ^ " variables.\n"); 
    if !time_out >= 0.0 
    then (let t = max 0.01 (!time_out -. (Sys.time () -. time)) in
          message 2 (fun _ -> "  Setting time out limit for SAT solver to remaining " ^ 
                              Printf.sprintf "%.2f" t ^ "sec\n");
          zchaff_SetTimeLimit zchaff t);
    message 2 (fun _ -> "  Solving ... ");
    let t = Sys.time () in
    let r = zchaff_Solve zchaff in
    message 2 (fun _ -> Printf.sprintf "%.2f" (Sys.time () -. t) ^ "sec\n"); 
    match r with
          2 -> message 2 (fun _ -> "  ");
               message 1 (fun _ -> problem.positiveReport lower_k upper_k);
	       if !continuous 
               then (message 2 (fun _ -> "  Deleting temporary constraints ... "); 
                     let t = Sys.time () in
                     zchaff_DeleteClauseGroup zchaff temporaryClauseGID;
                     message 2 (fun _ -> Printf.sprintf "%.2f" (Sys.time () -. t) ^ "sec\n"); 
                     run_engine (upper_k + 1) (upper_k + !step_width))
        | 1 -> message 2 (fun _ -> "  ");
               message 1 (fun _ -> problem.negativeReport lower_k upper_k);
               message 2 (fun _ -> "  Deleting temporary constraints ... "); 
               let t = Sys.time () in
               zchaff_DeleteClauseGroup zchaff temporaryClauseGID;
               message 2 (fun _ -> Printf.sprintf "%.2f" (Sys.time () -. t) ^ "sec\n"); 
               run_engine (upper_k + 1) (upper_k + !step_width)
	| 3 -> message 2 (fun _ -> "SAT Solver timeout!\n"); exit 3
	| 5 -> message 2 (fun _ -> "SAT Solver aborted by user!\n"); exit 5
	| 4 -> message 2 (fun _ -> "SAT Solver ran out of memory!\n"); exit 4
	| 0 -> message 2 (fun _ -> "Undetermined answer from the SAT Solver!\n"); exit 6
	| _ -> message 2 (fun _ -> "Unknown answer from the SAT solver!\n"); exit 6)
  in
  if (!start > 1)
  then (message 2 (fun _ -> "Creating permanent constraints for range [1.." ^ string_of_int (!start-1) ^ "] ..... "); 
        let t = Sys.time () in
        List.iter
          (fun cm -> let constraints = cm 0 (!start-2) in
                  List.iter
                    (fun c -> message 3 (fun _ -> "  Adding clause " ^ showClause c ^ "\n");
                              zchaff_AddClause zchaff c permanentClauseGID)
                    constraints)
          problem.permanent;
       message 2 (fun _ -> Printf.sprintf "%.2f" (Sys.time () -. t) ^ "sec\n")); 
  run_engine (!start-1) (!start + !step_width - 2);
  message 2 (fun _ -> "Execution time: " ^ Printf.sprintf "%.2f" (Sys.time () -. time) ^ " seconds.\n");
  Varencoding.showAllValues ();
  if !bound_reached then exit 1;
  if !time_limit_reached then exit 2;
  exit 0   
