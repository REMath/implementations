open Cil_types
open Cil
open TaintGamma

module InstrComputer(Param:sig
                        val globals : global list
                        val func_hash : (string, fundec) Hashtbl.t
                        val fmt : Format.formatter
                        val debug : bool      
                        val info : bool 
                        val main_func_name : string option
                     end) = struct
    module P = TaintPrinter.Printer(struct
                                        let fmt = Param.fmt
                                        let debug = Param.debug
                                        let info = Param.info
                                    end)
                
    module TH = TypeHelper.TypeComparer(struct
                                            let fmt = Param.fmt
                                            let debug = Param.debug
                                            let info = Param.info
                                        end)  
    module TG = TypeHelper.TypeGetter(struct
                                            let fmt = Param.fmt
                                            let debug = Param.debug
                                            let info = Param.info
                                        end)  
    module Typing = TaintTyping.Typing(struct
                                         let fmt = Param.fmt
                                         let debug = Param.debug
                                         let info = Param.info
                                        end)
    module Alias = Alias.AliasAnalysis(struct
                                         let fmt = Param.fmt
                                         let debug = Param.debug
                                         let info = Param.info
                                        end)
    
    (* This function returns the list of global variables. *)
    let list_global_vars () =
        let globals = List.fold_left
                        (fun result global ->
                            match global with
                                | GVar (vinfo, _, _) -> vinfo :: result
                                | _ -> result)
                        []
                        Param.globals in
        let globals = List.rev globals in
        let _list_global_vars () =
            globals
        in
        _list_global_vars
    
    (* Creates an intial environment for a function. *)
    (* The formals, locals, globals and the return value are initialized. *)
    let create_initial_env_func func = 
        let initial_env = Gamma.create_env () in
        (List.iter
            (fun formal ->
                ignore (Typing.process_formal initial_env formal))
            func.sformals);  
        (List.iter 
            (fun local ->
                ignore (Typing.process_local initial_env local))
            func.slocals);
        (List.iter
            (fun global ->
                ignore (Typing.process_global initial_env global))
            (list_global_vars () ()));
        let ret_taint = List.fold_left
                            (fun t formal ->
                                Typing.combine_taint t (G [formal]))
                            U
                            func.sformals in
        let ret_taint = List.fold_left
                            (fun t global ->
                                Typing.combine_taint t (G [global]))
                            ret_taint
                            (list_global_vars () ()) in 
        ignore (Typing.process_function_return initial_env func.svar ret_taint);
        initial_env
    
    (* Creates an intial environment for the main function. *)
    (* The formals, locals, globals and the return value are initialized. *)
    let create_initial_env_main func = 
        let initial_env = Gamma.create_env () in
        (List.iter
            (fun formal ->
                ignore (Gamma.set_taint initial_env formal.vid T))
            func.sformals);  
        (List.iter 
            (fun local ->
                ignore (Typing.process_local initial_env local))
            func.slocals);
        (List.iter
            (fun global ->
                ignore (Typing.process_global initial_env global))
            (list_global_vars () ()));
        let ret_taint = T in
        ignore (Typing.process_function_return initial_env func.svar ret_taint);
        initial_env
    
    (* Creates an intial environment for a function. *)
    (* The formals, locals, globals and the return value are initialized. *)
    let create_initial_env func = 
        match Param.main_func_name with 
        | None -> create_initial_env_func func
        | Some main_name -> 
            if main_name = func.svar.vname then
                create_initial_env_main func
            else
                create_initial_env_func func
    
    (* Performs the function call and returns the taintedness for the result. *)
    (* Params: *)
    (* env - the current function environment *)
    (* vinfo - the variable info for the function being called *)
    (* param_exprs - the list of parameter expressions for the callee *)
    (* func_envs - already computed environments *)
    let rec do_get_function_call_taint env vinfo param_exprs func_envs =
        let p_exp_length = List.length param_exprs in        
        (* Local function used for finding the actual parameter passed for a *)
        (* formal one. *)
        let find_binding actuals formals dep =
            let (i, _) = List.fold_left
                        (fun (idx, found) f ->
                            match found with
                                | true -> (idx, found)
                                | false ->
                                    if dep.vname = f.vname then (idx, true)
                                    else (idx + 1, false))
                        (0, false)
                        formals in
            List.nth actuals i
                
        in
        (* Local function used for instantiating all the formal parameter taints *)
        (* and global taints according to actual parameter taints and global taints *)
        (* from the current environment. *)
        let instantiate_call_taint env callee_env actuals formals vid =
            match Gamma.get_taint callee_env vid with
                | T -> T
                | U -> U
                | (G g) ->
                    List.fold_left
                        (fun t dep ->
                            try 
                                let param_expr = find_binding actuals formals dep in
                                let param_taint = do_expr env param_expr [] func_envs in
                                Typing.combine_taint t param_taint
                            with Failure _ ->
                                (* A global is used as a dependency. *)
                                Typing.combine_taint t (Gamma.get_taint env dep.vid))
                        U
                        g
        in
        (* Deals with pointer parameters as if they are return values. *)
        let do_pointer_params func callee_env =
            let formals = func.sformals in
            ignore (List.fold_left
                (fun idx formal ->
                    if idx >= p_exp_length then
                        idx + 1
                    else
                        if TG.is_return_param formal.vtype == false then idx + 1
	                    else
	                        let actual_param = TG.get_actual_param 
	                                            (find_binding param_exprs formals formal) in
	                        (match actual_param with
	                            | None -> ignore ()
	                            | Some a_vinfo ->
                                    let a_taint = instantiate_call_taint env callee_env param_exprs formals formal.vid in
                                    Gamma.set_taint env a_vinfo.vid a_taint);
                            idx + 1)
                0
                formals)
        in
        (* Deals with globals as if they are return values. *)
        let do_globals func callee_env =
            let formals = func.sformals in
            List.iter
                (fun global ->
                    let g_taint = instantiate_call_taint env callee_env param_exprs formals global.vid in
                    Gamma.set_taint env global.vid g_taint)
                (list_global_vars () ())
        in
        (* Computes the taintedness of the return value for the given function. *)
        let do_return func callee_env =
            let formals = func.sformals in
            let ret_taint = instantiate_call_taint env 
                                callee_env 
                                param_exprs 
                                formals 
                                (Typing.get_function_return_vid func.svar) in
            ret_taint
        in
        let func = Hashtbl.find Param.func_hash vinfo.vname in
        let (callee_env, _) = Inthash.find func_envs func.svar.vid in
        do_pointer_params func callee_env;
        do_globals func callee_env;
        do_return func callee_env
    
    and do_offset env offset func_envs =
        match offset with
            | NoOffset -> 
                U
            | Field _ -> 
                U
            | Index (idx_exp, idx_offset) ->
                let idx_taint = do_expr env idx_exp [] func_envs in
                let idx_offset_taint = do_offset env idx_offset func_envs in
                Typing.combine_taint idx_taint idx_offset_taint
    
    (* Returns the taintedness for a lvalue. *)
    (* Params: *)
    (* env - the current environment *)
    (* lvalue - the lvalue being analyzed *)
    (* param_exprs - contains the list of param expressions in the case that *)
    (* lvalue contains a function call *)
    (* func_envs - the environments for already computed functions *)    
    and get_lvalue_taint env lvalue param_exprs func_envs =
        let get_lvalue_taint_vinfo vinfo offset =
            let taint = 
                try
                    Gamma.get_taint env vinfo.vid 
                with Not_found ->
                    try
                        do_get_function_call_taint env vinfo param_exprs func_envs
                    with Not_found ->
                        P.print () "[ERROR] Cannot find lvalue: %s\n" vinfo.vname;
                        T 
            in
            let offset_taint = do_offset env offset func_envs in
            let taint = Typing.combine_taint taint offset_taint in
            P.print_debug () "[DEBUG] Taint for lvalue %s: " vinfo.vname;
            P.print_taint_debug () taint; 
            taint
        in
        (* Gets the taint for a lvalue that is a memory location. I.e.: a pointer. *)
        let get_lvalue_taint_mem expr offset =
            let taint = do_expr env expr [] func_envs in
            let offset_taint = do_offset env offset func_envs in
            let taint = Typing.combine_taint taint offset_taint in
            P.print_debug () "[DEBUG] Taint for memory lvalue: %s" "\n";
            P.print_taint_debug () taint; 
            taint
        in
        P.print_info () "[INFO] Getting lvalue taint %s" "\n";
        match lvalue with
            | ((Var vinfo), offset) -> get_lvalue_taint_vinfo vinfo offset
            | ((Mem exp), offset) -> get_lvalue_taint_mem exp offset         
    and
    (* Returns the taintedness of an expression according to the environment. *)
    (* Params: *)
    (* env - the current environment *)
    (* expr - the expression to be analyzed *)
    (* param_exprs - contains the list of parameter expressions if the current *)
    (* expression contains a function call *)
    (* func_envs - the previously computed function environments *)
    do_expr env expr param_exprs func_envs =
        let do_const () =
            P.print_debug () "%s" "[DEBUG] Taint for Constant is: ";
            P.print_taint_debug () U;
            U
        in
        let do_lvalue lvalue =
            let taint = get_lvalue_taint env lvalue param_exprs func_envs in
            P.print_debug () "%s" "[DEBUG] Taint for Lvalue is: ";
            P.print_taint_debug () taint;
            taint
        in
        let do_sizeOf () =
            P.print_debug () "%s" "[DEBUG] Taint for SizeOf is: ";
            P.print_taint_debug () U;
            U
        in
        let do_sizeOfE expr =
            let taint = do_expr env expr param_exprs func_envs in
            P.print_debug () "%s" "[DEBUG] Taint for SizeOfE is: ";
            P.print_taint_debug () taint; 
            taint
        in
        let do_sizeOfStr () =
            P.print_debug () "%s" "[DEBUG] Taint for SizeOfStr is: ";
            P.print_taint_debug () U;
            U
        in
        let do_alignOf () =
            P.print_debug () "%s" "[DEBUG] Taint for AlignOf is: ";
            P.print_taint_debug () U;
            U
        in
        let do_alignOfE () =
            P.print_debug () "%s" "[DEBUG] Taint for AlignOfE is: ";
            P.print_taint_debug () U;  
            U
        in
        let do_unOp expr =
            let taint = do_expr env expr param_exprs func_envs in
            P.print_debug () "%s" "[DEBUG] Taint for UnOp is: ";
            P.print_taint_debug () taint; 
            taint
        in
        let do_binOp expr1 expr2 =
            let taint = Typing.combine_taint 
                            (do_expr env expr1 param_exprs func_envs) 
                            (do_expr env expr2 param_exprs func_envs) in
            P.print_debug () "%s" "[DEBUG] Taint for BinOp is: ";
            P.print_taint_debug () taint; 
            taint
        in
        let do_castE typ expr =
            let taint =
                match TH.check_type typ expr with
                    | true -> do_expr env expr param_exprs func_envs
                    | false -> T in
            P.print_debug () "%s" "[DEBUG] Taint for CastE is: ";
            P.print_taint_debug () taint;   
            taint
        in
        let do_addrOf lvalue =
            let taint = get_lvalue_taint env lvalue param_exprs func_envs in
            P.print_debug () "%s" "[DEBUG] Taint for AddrOf is: ";
            P.print_taint_debug () taint; 
            taint
        in
        let do_startOf lvalue = 
            let taint = get_lvalue_taint env lvalue param_exprs func_envs in
            P.print_debug () "%s" "[DEBUG] Taint for StartOf is: ";
            P.print_taint_debug () taint;  
            taint
        in
        let do_info () =
            P.print_debug () "%s" "[DEBUG] Taint for Info is: ";
            P.print_taint_debug () U;
            U
        in
        
        P.print_info () "[INFO] Processing instruction %s" "\n"; 
        match expr with
            | Const _ -> do_const ()  
            | Lval lvalue -> do_lvalue lvalue                    
            | SizeOf _ -> do_sizeOf ()                    
            | SizeOfE s_expr -> do_sizeOfE s_expr                    
            | SizeOfStr _ -> do_sizeOfStr ()
            | AlignOf _ -> do_alignOf ()
            | AlignOfE _ -> do_alignOfE ()
            | UnOp (_, un_expr, _) -> do_unOp un_expr
            | BinOp (_, bin_expr1, bin_expr2, _)  -> do_binOp bin_expr1 bin_expr2
            | CastE (typ, expr)-> do_castE typ expr
            | AddrOf lvalue -> do_addrOf lvalue
            | StartOf lvalue -> do_startOf lvalue
            | Info _ -> do_info ()
    
    (* Processes a nullable expression. If the expression is null U is returned, *)
    (* otherwise the taintedness of the expression is returned. *)
    (* Params: *)
    (* env - the current environment *)
    (* null_expr - a possibly null expression *)
    (* param_exprs - contains the list of parameter expressions when the null_expr *)
    (* has a function call *)
    (* func_envs - the previously computed function environments *)
    let do_null_expr env null_expr param_exprs func_envs =
        let do_null () =
            P.print_debug () "%s" "[DEBUG] Taint for Null expr is: ";
            P.print_taint_debug () U; 
            U
        in
        let do_not_null expr =
            let taint = do_expr env expr param_exprs func_envs in
            P.print_debug () "%s" "[DEBUG] Taint for NotNull expr is: ";
            P.print_taint_debug () taint; 
            taint
        in
        
        P.print_info () "[INFO] Processing nullable expression %s" "\n"; 
        match null_expr with
            | None -> do_null ()
            | Some expr -> do_not_null expr 
    
    (* Changes the mapping for lvalue in the given environment according to cond_taint*)
    (* and the assigned expression. *)
    (* Params: *)
    (* env - the current environment *)
    (* expr - the rvalue expression *)
    (* cond_taint - the current condition taint *)
    (* param_exprs - contains the list of parameter expressions when expr has a *)
    (* function call *)
    (* func_env - the previously computed function environments *)
    let do_assign env lvalue expr cond_taint param_exprs func_env =
        let do_assign_lvalue_tainted vinfo offset =
            P.print_debug () "[DEBUG] Assigning T to %s\n" vinfo.vname; 
            let aliases = Alias.get_aliases vinfo in
            List.iter 
                (fun info -> Gamma.set_taint env info.vid T)
                aliases;
            env
        in
        let do_assign_lvalue vinfo expr offset =
            let expr_taint = do_expr env expr param_exprs func_env in
            let offset_taint = do_offset env offset func_env in
            P.print_debug () "[DEBUG] Assigning to %s taint:" vinfo.vname;
            P.print_taint_debug () expr_taint; 
            (* If the symbol is a structure or array which was tainted, *)
            (* we must combine the old taint too. *)
            let prev_taint = 
                match offset with 
                | NoOffset -> U
                | _ -> Gamma.get_taint env vinfo.vid in
            let taint = Typing.combine_taint expr_taint cond_taint in
            let taint = Typing.combine_taint taint offset_taint in
            let taint = Typing.combine_taint taint prev_taint in
            let aliases = Alias.get_aliases vinfo in
            List.iter 
                (fun info -> Gamma.set_taint env info.vid taint)
                aliases;
            env
        in
        let do_assign_lvalue_mem_tainted ptr_expr =
            let vinfo = Utils.extract_vinfo_from_ptr_expr ptr_expr in
            P.print_debug () "[DEBUG] Assigning T to %s\n" vinfo.vname; 
            let aliases = Alias.get_aliases vinfo in
            List.iter 
                (fun info -> Gamma.set_taint env info.vid T)
                aliases;
            env
        in
        let do_assign_lvalue_mem ptr_expr expr offset =
            let vinfo = Utils.extract_vinfo_from_ptr_expr ptr_expr in
            let vinfo_expr_taint = do_expr env ptr_expr [] func_env in
            let expr_taint = do_expr env expr param_exprs func_env in
            P.print_debug () "[DEBUG] Assigning to %s taint:" vinfo.vname;
            P.print_taint_debug () expr_taint; 
            (* If the symbol is a structure or array which was tainted, *)
            (* we must combine the old taint too. *)
            let prev_taint = 
                match offset with 
                | NoOffset -> U
                | _ -> Gamma.get_taint env vinfo.vid in
            let taint = Typing.combine_taint expr_taint cond_taint in
            let taint = Typing.combine_taint taint vinfo_expr_taint in
            let taint = Typing.combine_taint taint prev_taint in
            let aliases = Alias.get_aliases vinfo in
            List.iter 
                (fun info -> Gamma.set_taint env info.vid taint)
                aliases;
            env
        in
        
        P.print_info () "[INFO] Processing assign instruction %s" "\n"; 
        match (lvalue, cond_taint) with
            | ((Var vinfo, offset), T) -> do_assign_lvalue_tainted vinfo offset                   
            | ((Var vinfo, offset), _) -> do_assign_lvalue vinfo expr offset
            | ((Mem ptr_expr, _), T) -> do_assign_lvalue_mem_tainted ptr_expr
            | ((Mem ptr_expr, offset), _) -> do_assign_lvalue_mem ptr_expr expr offset   
            
    (* Params: *)
    (* env - the current environment *)
    (* null_lval - the nullable lvalue *)
    (* cast_expr - the expression containing the call *)
    (* cond_taint - the current condition taint *)
    (* func_envs - the previously computed environments *)
    let do_call env null_lval cast_expr param_exprs cond_taint func_envs =
        (* TODO: BUG_LVAL_PTR: Missed the case where the lvalue is a pointer *)
        (* TODO: Check if fix is OK. *)
        (* let do_call_lval vinfo =
            let taint = do_expr env cast_expr param_exprs func_envs in
            let taint = Typing.combine_taint taint cond_taint in
            Gamma.set_taint env vinfo.vid taint;
            P.print_debug () "[DEBUG] Assigning to %s taint value:" vinfo.vname;
            P.print_taint_debug () taint; 
            env
        in *) 
        let do_call_lval lval =
            do_assign env lval cast_expr cond_taint param_exprs func_envs
        in
        let do_call_void () =
            P.print_debug () "%s\n" "[DEBUG] Processing void call";
            ignore (do_expr env cast_expr param_exprs func_envs); 
            env 
        in

        P.print_info () "[INFO] Processing call instruction %s" "\n";         
        match null_lval with
            (* TODO: BUG_LVAL_PTR: Missed the case where the lvalue is a pointer *)
            (* TODO: Check if fix is OK. *)
            (* | Some (Var vinfo, _) -> do_call_lval vinfo *)
            | Some lval -> do_call_lval lval
            | _ -> do_call_void ()
    
    (* Changes the environment according to the instruction *)
    let do_instr env instr cond_taint func_envs =
        P.print_info () "[INFO] Processing instruction %s" "\n"; 
        match instr with
            | (Set (lvalue, expr, _))
                -> do_assign env lvalue expr cond_taint [] func_envs
            | (Call (null_lval, cast_expr, param_exprs, _))
                (* Make the assumption that all the functions return a single value. *)
                -> do_call env null_lval cast_expr param_exprs cond_taint func_envs
            | _ -> env 
        
    (* Changes the return value in the environment according to the return expression *)
    let do_return_instr env func null_expr cond_taint func_envs =
        let fname = func.svar.vname in
        let fid = func.svar.vid in
        P.print_info () "[INFO] Processing return instruction for function %s\n" fname; 
        let old_taint = 
            (try 
                Gamma.get_taint env fid
            with Not_found -> U)
        in
        let new_taint = (Typing.combine_taint 
                            old_taint 
                            (Typing.combine_taint 
                                cond_taint 
                                (do_null_expr env null_expr [] func_envs))) in
        Gamma.set_taint env (-fid) new_taint;
        P.print_debug () "[DEBUG] FID: %d\n" fid;
        P.print_debug () "[DEBUG] Old taint for return in function %s:" fname;
        P.print_taint_debug () old_taint;
        P.print_debug () "[DEBUG] New taint for return in function %s:" fname;
        P.print_taint_debug () new_taint;   
        env
        
    (* Only return the taintedness of the expression. The successors will be computed*)
    (* later. *)
    let do_if_instr env expr true_block false_block cond_taint func_env =
        P.print_info () "[INFO] Processing if instruction %s" "\n"; 
        let expr_taint = do_expr env expr [] func_env in 
        let new_cond_taint = Typing.combine_taint expr_taint cond_taint in
        P.print_debug () "%s" "[DEBUG] Condition taint for if instruction:";
        P.print_taint_debug () cond_taint;
        P.print_debug () "%s" "[DEBUG] New condition taint for if instruction:";
        P.print_taint_debug () new_cond_taint; 
        new_cond_taint
        
    (* Only return the taintedness of the expression. The successors will be computed*)
    (* later. *)
    let do_switch_instr env expr cond_taint func_env =
        P.print_info () "[INFO] Processing switch instruction %s" "\n"; 
        let expr_taint = do_expr env expr [] func_env in 
        let new_cond_taint = Typing.combine_taint expr_taint cond_taint in
        P.print_debug () "%s" "[DEBUG] Condition taint for if instruction:";
        P.print_taint_debug () cond_taint;
        P.print_debug () "%s" "[DEBUG] New condition taint for if instruction:";
        P.print_taint_debug () new_cond_taint;  
        new_cond_taint
        
    let do_loop_instr env stmt_block stmt_continue stmt_break cond_taint =
        P.print_info () "[INFO] Processing loop instruction %s" "\n"; 
        (env, cond_taint)                     
end