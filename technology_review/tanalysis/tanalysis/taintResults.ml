open Cil_types
open Cil
open TaintGamma
open VulnerableUtils

module ResultsComputer(Param:sig
                        val globals : global list     
                        val func_envs : functionEnvironment
                        val func_hash : (string, fundec) Hashtbl.t 
                        val func_constr_hash : taintConstraints Inthash.t
                        val fmt : Format.formatter
                        val debug : bool      
                        val info : bool     
                     end) = struct
    
    module SC = TaintInstructionComputer.InstrComputer(struct
                                                            let globals = Param.globals
                                                            let func_hash = Param.func_hash
                                                            let fmt = Param.fmt
                                                            let debug = Param.debug
                                                            let info = Param.info
                                                            let main_func_name = None
                                                        end)
    
    module Typing = TaintTyping.Typing (struct
	                    let fmt = Param.fmt
	                    let debug = Param.debug      
	                    let info = Param.info     
	                 end)
                    
    module TG = TypeHelper.TypeGetter(struct
                                            let fmt = Param.fmt
                                            let debug = Param.debug
                                            let info = Param.info
                                        end)  

    module P = TaintPrinter.Printer(struct
                                        let fmt = Param.fmt
                                        let debug = Param.debug
                                        let info = Param.info
                                    end) 

    type func_frame = Frame of fundec
    type func_stack = func_frame list 

    let stmt_count = ref 0;;

    let inc_stmt_count () =
        stmt_count := !stmt_count + 1

    let taint_stmt_count = ref 0;;

    let vulnerable_statements = ref [];;

    let add_vulnerable_statement_function_constraint stmt fname =
        vulnerable_statements := (FunctionConstraint (stmt, fname))::!vulnerable_statements
        
    let add_vulnerable_statement_buffer_index stmt bufname =
        vulnerable_statements := (BufferIndex (stmt, bufname))::!vulnerable_statements

    let inc_taint_stmt_count () =
        taint_stmt_count := !taint_stmt_count + 1

    let check_tainted taint stmt = 
        match taint with 
        | G _ -> 
            P.print () "WARNING: G reached in results check. Sid: %d:" stmt.sid;
            P.print_taint () taint;
            true
        | _ -> 
            Gamma.compare_taint taint T

    let rec do_instr env_instance curr_stmt curr_func_stack func instr =
        let curr_stmt_env = Inthash.find env_instance curr_stmt.sid in
        let do_check_array_constraints lval =
            let rec do_check_array_offset offset =
                match offset with
                | NoOffset -> 
                    P.print_info () "%s\n" "[INFO] Found no offset for lvalue.";
                    true
                | Field (_, inner_offset) ->
                    P.print_info () "%s\n" "[INFO] Found field offset for lvalue."; 
                    do_check_array_offset inner_offset
                | Index (expr, inner_offset) ->
                    P.print_info () "%s\n" "[INFO] Found index offset for lvalue.";
                    let expr_taint = SC.do_expr curr_stmt_env expr [] Param.func_envs in
                    P.print_info () "%s" "[INFO] Taint value for index: ";
                    P.print_taint_info () expr_taint;
                    (match check_tainted expr_taint curr_stmt with
                    | true -> false
                    | false -> do_check_array_offset inner_offset)
            in
            
            match lval with
            | (Var vinfo, offset) ->
                P.print_info () "%s" "[INFO] Checking array offset for lvalue:\n";
                (match do_check_array_offset offset with
                | false -> add_vulnerable_statement_buffer_index curr_stmt vinfo.vname
                | true -> ignore ())
            | (Mem exp, offset) ->
                P.print_info () "%s" "[INFO] Checking array offset for pointer\n";
                (match do_check_array_offset offset with
                (* TODO: extract pointer name from expression exp *)
                | false -> add_vulnerable_statement_buffer_index curr_stmt "pointer"
                | true -> ignore ())
        in
        let do_assign lval =
            let vinfo = Utils.get_lval_vinfo lval in
                if (check_tainted
                        (Gamma.get_taint
                            curr_stmt_env
                            vinfo.vid)
                        curr_stmt) then (
                    P.print_info () "[INFO] Checking array constraints for lval %s\n" vinfo.vname;
                    do_check_array_constraints lval;
                    inc_taint_stmt_count ();
                    true
                ) else (
                    false
                )
        in
        let do_call null_lval call_expr param_exprs =
            let do_null_lval null_lval =
                match null_lval with
                    | None -> false
                    | Some lval -> do_assign lval
            in 
            let do_check_pointer_params func effect_added =
                if effect_added then (
                    ignore ()
                ) else (
                    let p_len = List.length param_exprs in
                    ignore (
                        List.fold_left 
                        (fun (idx, added) formal ->
                            if added || idx >= p_len then (idx + 1, added)
                            else
                                match TG.is_return_param formal.vtype with
                                | true ->
                                    (try 
                                        let p_expr = List.nth param_exprs idx in
		                                let expr_vinfo = Utils.extract_vinfo_from_ptr_expr p_expr in
		                                let taint = Gamma.get_taint curr_stmt_env expr_vinfo.vid in
                                        if check_tainted taint curr_stmt then (
                                            inc_taint_stmt_count ();
                                            (idx + 1, true)
                                        ) else (
                                            (idx + 1, false)
                                        )
                                    with Not_found ->
                                        (idx + 1, false))
                                | false ->
                                    (idx + 1, false))
                        (0, false)
                        func.sformals) )
            in  
            let get_caller_env () =
                let init_env = 
	                match List.length curr_stmt.preds with
	                | 0 -> curr_stmt_env
	                | _ -> Inthash.find env_instance (List.hd curr_stmt.preds).sid in
                List.fold_left
                    (fun env pred ->
                        Typing.combine env (Inthash.find env_instance pred.sid))
                    init_env
                    curr_stmt.preds 
            in
            let rec do_check_recursive_call func_stack callee_func =
                match func_stack with
                    | [] -> false
                    | (Frame f)::tl ->
                        if f.svar.vid == callee_func.svar.vid then true
                        else
                            do_check_recursive_call tl callee_func
            in
            let do_check_function_constraints callee_func taint_instances =
                let do_check_taint_constraint taint meta_taint =
                    match meta_taint with
                    | M_T -> true
                    | M_U -> if taint == U then true else false
                    | M_G g ->
                        let constr_taint = List.fold_left
                            (fun taint dep_name ->
                                try
                                    let (tiformal, titaint) 
                                        = List.find
                                            (fun (tiformal, _) -> dep_name = tiformal.vname)
                                            taint_instances in
                                    Typing.combine_taint taint titaint
                                with Not_found ->
                                    P.print () "[WARNING] Unable to find constraint dependency: %s\n" dep_name;
                                    taint) 
                            U
                            g in
                        match (constr_taint, taint) with
                        | (T, _) -> true
                        | (G _, _) -> true
                        | (U, U) -> true
                        | _ -> false
                in
                
                if Inthash.mem Param.func_constr_hash callee_func.svar.vid then (
	                P.print_info () "[INFO] Checking function constraint for function %s\n" callee_func.svar.vname;
	                let func_constraints = Inthash.find Param.func_constr_hash callee_func.svar.vid in
	                let holds = 
	                    List.fold_left
	                        (fun holds (formal_name, cons_f_meta_taint) ->
	                            match holds with
	                            | false -> false
	                            | true ->
	                                P.print_info () "[INFO] Searching for formal %s\n" formal_name;
		                            try
		                                let (tiformal, titaint) 
		                                    = List.find
		                                        (fun (tiformal, _) -> formal_name = tiformal.vname)
		                                        taint_instances in
	                                    P.print_info () "%s" "[INFO] Actual taint is: ";
	                                    P.print_taint_info () titaint;
	                                    do_check_taint_constraint titaint cons_f_meta_taint
	                                with Not_found ->
	                                    P.print_info () "[INFO] Formal %s not found\n" formal_name;
	                                    true)
	                        true
	                        func_constraints in
	                P.print_info () "[INFO] Constraints hold for function %s: %B\n" callee_func.svar.vname holds;
	                match holds with
                  | false -> add_vulnerable_statement_function_constraint curr_stmt callee_func.svar.vname
	                | true -> ignore ())
            in
            let do_function_call callee_func =
                P.print_info () "[INFO] Doing function call for function %s\n" callee_func.svar.vname;
                let caller_env = get_caller_env () in
                let p_len = List.length param_exprs in
                (* Create the list of taint instances formal params + globals. *)
                P.print_info () "[INFO] Creating taint instances list for %s\n" callee_func.svar.vname;
                let (_, taint_instances) = 
                    List.fold_left
                        (fun (idx, instances) formal ->
                            if idx >= p_len then (idx + 1, instances)
                            else
                                let p_expr = List.nth param_exprs idx in
                                let f_taint = SC.do_expr caller_env p_expr [] Param.func_envs in
                                (idx + 1, (formal, f_taint)::instances))
                        (0, [])
                        callee_func.sformals in
                let taint_instances = 
                    List.fold_left
                        (fun instances global ->
                            let g_taint = Gamma.get_taint caller_env global.vid in
                            (global, g_taint)::instances)
                        taint_instances
                        (SC.list_global_vars () ()) in
                (* Check if the called function parameters hold the constraints for the callee. *)
                P.print_info () "[INFO] Checking function constraints for %s\n" callee_func.svar.vname;
                do_check_function_constraints callee_func taint_instances;
                let (_, callee_env) = Inthash.find Param.func_envs callee_func.svar.vid in
                (* Create the context dependent environment for the callee. *)
                P.print_info () "[INFO] Instantiating function env for %s\n" callee_func.svar.vname;
                let callee_env = Typing.instantiate_func_env callee_env taint_instances in
                let new_worklist =
                    match List.length callee_func.sallstmts with
                        | 0 -> []
                        | _ -> [List.hd callee_func.sallstmts] in
                let new_visited_ref = ref (Inthash.create 1024) in
                P.print_info () "[INFO] Checking if the call to %s is recursive\n" callee_func.svar.vname;
                match do_check_recursive_call curr_func_stack callee_func with
                    | false ->
                        P.print_info () "Analyzing results for function %s\n" callee_func.svar.vname;
                        compute callee_env 
                            ((Frame func)::curr_func_stack) 
                            (callee_func, new_visited_ref, new_worklist)
                    | true ->
                        P.print_info () "Ignoring recursive function call to %s\n" callee_func.svar.vname;
                        ignore ()
            in
                        
            let effect_added = do_null_lval null_lval in
            let finfo = Utils.get_lval_vinfo (Utils.extract_lvalue_from_expr call_expr) in
            try 
	            let callee_func = Hashtbl.find Param.func_hash finfo.vname in
	            do_check_pointer_params callee_func effect_added;
	            do_function_call callee_func
            with Not_found ->
                ignore () 
        in
        
        inc_stmt_count ();
        match instr with
            | Set (lval, _, _) ->
                ignore (do_assign lval)        
            | Call (null_lval, call_expr, param_exprs, _) ->
                do_call null_lval call_expr param_exprs
            | _ -> ignore ()

    and do_return env_instance curr_stmt func null_expr =
        let curr_stmt_env = Inthash.find env_instance curr_stmt.sid in
        inc_stmt_count ();
        match null_expr with
            | None -> 
                ignore ()
            | Some _ -> 
                if (check_tainted 
                        (Gamma.get_taint 
                            curr_stmt_env 
                            (Typing.get_function_return_vid func.svar))
                        curr_stmt) then
                    inc_taint_stmt_count ()

    and do_stmt env_instance curr_func_stack func visited_ref curr_stmt =
        let visited = 
            try
                Inthash.find !visited_ref curr_stmt.sid
            with Not_found ->
                Inthash.add !visited_ref curr_stmt.sid true;
                false in
        if visited then (
            []
        ) else ( 
	        match curr_stmt.skind with
	            | Instr instr -> 
	                do_instr env_instance curr_stmt curr_func_stack func instr;
                    curr_stmt.succs
	            | Return (null_expr, _) -> 
	                do_return env_instance curr_stmt func null_expr;
                    curr_stmt.succs
	            | If _ -> 
	                curr_stmt.succs
	            | Switch _ ->
	                curr_stmt.succs
	            | Loop _ -> 
	                curr_stmt.succs
	            | Block block ->
	                List.fold_left 
	                    (fun succs s -> 
                            let new_succs = do_stmt env_instance curr_func_stack func visited_ref s in
                            List.append succs new_succs)
                        []
	                    block.bstmts
	            | _ -> 
	                curr_stmt.succs
        )
        
    and compute env_instance curr_func_stack (func, visited_ref, worklist) =
        match List.length worklist with
        | 0 -> 
            P.print_info () "Finished analyzing function %s\n" func.svar.vname;
            P.print_info () "%s" "Current stack: ";
            List.iter
                (fun (Frame f) ->
                    P.print_info () "%s, " f.svar.vname)
                (List.rev curr_func_stack);
            P.print_info () "%s" "\n";
            ignore ()
        | _ -> 
            let curr_stmt = List.hd worklist in
            match do_stmt env_instance curr_func_stack func visited_ref curr_stmt with
            | [] ->
                compute env_instance
                    curr_func_stack
                        (func, visited_ref, List.tl worklist)
            | succs ->
                compute env_instance 
                    curr_func_stack 
                        (func, visited_ref, List.append (List.tl worklist) succs)
            
end

let get_main_func globals =
        (* TODO: remove hardcoding for entry point *)
        match List.fold_left
            (fun result g ->
                match result with
                    | Some _ -> result
                    | None -> 
                        match g with
                            | GFun (funcdec, _) when funcdec.svar.vname = "main" -> Some funcdec
                            | _ -> None)
            None
            globals with
        | None -> failwith "[FATAL]: TAINT RESULTS: Missing main function."
        | Some result -> result

let get_results format dbg inf f_envs f_hash gls f_constr_hash =
    let module Computer = ResultsComputer(struct
					                        let globals = gls
					                        let func_envs = f_envs
					                        let func_hash = f_hash
                                  let func_constr_hash = f_constr_hash 
					                        let fmt = format
					                        let debug = dbg      
					                        let info = inf     
					                     end) in
    let main_func = get_main_func gls in
    let (_, main_instance) = Inthash.find f_envs main_func.svar.vid in
    let worklist = 
        match List.length main_func.sallstmts with
            | 0 -> []
            | _ -> [List.hd main_func.sallstmts] in
    let visited_ref = ref (Inthash.create 1024) in
    Printf.printf "%s\n" "Analyzing results for function main";
    Computer.compute main_instance [] (main_func, visited_ref, worklist);
    let vulnerable_statements = 
      List.sort 
        (fun v1 v2 -> VulnerableUtils.compare v1 v2)
        !Computer.vulnerable_statements in                  
    (!Computer.stmt_count, !Computer.taint_stmt_count, vulnerable_statements)
