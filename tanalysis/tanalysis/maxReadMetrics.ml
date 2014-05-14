(* TODO: OBSOLETE better implementation required sept-2009 *)

open Cil
open Cilutil
open Cil_types
open MetricComputer

(* Simple Read Metric Part *)
module MaxReadMetric = struct
    type read_non_cyclic_metric = NonCyclic of int
    type read_cyclic_metric = Cyclic of int
    type read_metric = ReadMetric of (read_non_cyclic_metric * read_cyclic_metric)
    
    let has_read_call stmt =
        (* TODO remove hardcoding *)
        match stmt.skind with
        | Instr (Call (_, call_exp, _, _)) ->
            let vinfo = Utils.get_lval_vinfo (Utils.extract_lvalue_from_expr call_exp) in
            if vinfo.vname = "taint" then true else false
        | _ -> false
    
    let compare 
        (ReadMetric (NonCyclic nc1, Cyclic c1)) 
        (ReadMetric (NonCyclic nc2, Cyclic c2)) =
            if nc1 - nc2 = 0 then
                c1 - c2
            else
                nc1 - nc2
    
    let equal
        (ReadMetric (NonCyclic nc1, Cyclic c1)) 
        (ReadMetric (NonCyclic nc2, Cyclic c2)) =
            if nc1 = nc2 && c1 == c2 then true else false

    let default = ReadMetric (NonCyclic 0, Cyclic 0)

    let zero = default
    
    let add 
        (ReadMetric (NonCyclic nc1, Cyclic c1)) 
        (ReadMetric (NonCyclic nc2, Cyclic c2)) =
            (ReadMetric (NonCyclic (nc1 + nc2), Cyclic (c1 + c2)))

    let sub 
        (ReadMetric (NonCyclic nc1, Cyclic c1)) 
        (ReadMetric (NonCyclic nc2, Cyclic c2)) =
            (ReadMetric (NonCyclic (nc1 - nc2), Cyclic (c1 - c2)))
            
    let add_second_in_loop
        (ReadMetric (NonCyclic nc1, Cyclic c1)) 
        (ReadMetric (NonCyclic nc2, _)) =
            (ReadMetric (NonCyclic nc1, Cyclic (c1 + nc2)))

    let node_value stmt =
        match has_read_call stmt with
        | true 
            -> ReadMetric (NonCyclic (-1), Cyclic 0)
        | false
            -> default

    let edge_value stmt_src stmt_dst =
        node_value stmt_dst        
        
    let print_value (ReadMetric (NonCyclic nc, Cyclic c)) =
        Printf.printf "ReadMetric (NonCyclic %d, Cyclic %d)\n" (-nc) (-c)
    
    let get_path_bound_stmts f_hash = 
    (* TODO: remove hard-coding for main entry point *)
    let main_func = Hashtbl.find f_hash "main" in
    let start = 
        match main_func.sallstmts with
        | [] -> failwith "[ERROR][METRICS] No statements in main function"
        | start::_ -> start in
    (* TODO: Check for multiple return statements *)
    let end_stmts = 
        List.fold_left
            (fun res stmt ->
                match stmt.succs with
                | [] -> stmt :: res
                | _ -> res)
            []
            main_func.sallstmts in
    (start, List.hd end_stmts)  
end

let compute_max_read_metrics format dbg inf f_hash =
    let funcs = Hashtbl.fold
                    (fun name func result ->
                        func::result)
                    f_hash 
                    [] in
    let module MRM = MaxReadMetric in
    let module P = Printer.Printer(struct
	                                    let fmt = format
	                                    let debug = dbg
	                                    let info = inf
	                                end) in
    let module Computer = MetricComputer(struct
                        type t = MRM.read_metric
                        let func_hash = f_hash
                        let fmt = format
                        let debug = dbg    
                        let info = inf
                        let value_comparator = MRM.compare
                        let value_equal = MRM.equal
                        let value_default = MRM.default
                        let value_zero = MRM.zero
                        let value_add = MRM.add  
                        let value_sub = MRM.sub
                        let value_add_second_in_loop = MRM.add_second_in_loop
                        let node_value = MRM.node_value
                        let edge_value = MRM.edge_value   
                        let print_value = MRM.print_value
                     end) in
    let graph = Computer.create_graph funcs in
    let (new_graph, removed_edges) = Computer.break_loops graph in
    let (start_stmt, end_stmt) = MRM.get_path_bound_stmts f_hash in
    let (shortest_path, weight) = Computer.get_best_path new_graph start_stmt end_stmt in
    let (path_stmt_hash, weight) = Computer.add_removed_edges new_graph shortest_path weight removed_edges in
    MRM.print_value weight; 
    path_stmt_hash
