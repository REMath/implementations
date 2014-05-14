open Cil
open Cilutil
open Cil_types
open Graph

module MetricComputer(Param:sig
                        type t
                        val func_hash : (string, fundec) Hashtbl.t
                        val fmt : Format.formatter
                        val debug : bool      
                        val info : bool
                        val value_comparator : t -> t -> int 
                        val value_equal : t -> t -> bool
                        val value_default : t
                        val value_zero : t
                        val value_add : t -> t -> t
                        val value_sub : t -> t -> t
                        val value_add_second_in_loop : t -> t -> t
                        val node_value : stmt -> t
                        (* edge_value src dst *)
                        val edge_value : stmt -> stmt -> t  
                        val print_value : t -> unit  
                     end) = struct

    module P = Printer.Printer(struct
                                    let fmt = Param.fmt
                                    let debug = Param.debug
                                    let info = Param.info
                                end)

    type nodeType = Statement of stmt 
        | BeginCall of (fundec * stmt) 
        | EndCall of (fundec * stmt) 
    
    module VertexType = struct 
        type t = nodeType 
	end
    
	module LabelType = struct 
        type t = Param.t 
        let compare = Param.value_comparator 
        let hash = Hashtbl.hash 
        let equal = Param.value_equal
        let default = Param.value_default
	end
    
    module WeightType = struct 
        type label = Param.t
        type t = Param.t
        let weight x = x
        let zero = Param.value_zero
        let add = Param.value_add
        let compare = Param.value_comparator
    end
    
    module G = Imperative.Digraph.AbstractLabeled(VertexType)(LabelType) 
    module SCC = Components.Make(G)
    module Dij = Path.Dijkstra(G)(WeightType)
    
    let print_node vertex node_mappings =
        let node = Hashtbl.find node_mappings vertex in
        match node with
        | Statement stmt -> P.print () "Statement sid: %d\n" stmt.sid
        | BeginCall (func, stmt) -> P.print () "BeginCall (func, sid): (%s, %d)\n" func.svar.vname stmt.sid
        | EndCall (func, stmt) -> P.print () "EndCall (func, sid): (%s, %d)\n" func.svar.vname stmt.sid

    let print_node_info vertex node_mappings = 
        if Param.info then
            print_node vertex node_mappings 

    let print_sccs sccs node_mappings =
        let do_print_scc scc =
            P.print () "%s\n" "SCC:";
            List.iter
                (fun v ->
                    print_node v node_mappings;)
                scc;
            P.print () "%s\n" "=========="
        in
        List.iter 
            (fun scc -> do_print_scc scc)
            sccs
    
    let print_sccs_info sccs node_mappings =
        if Param.info then
            print_sccs sccs node_mappings
            
    let print_graph g node_mappings =
        G.iter_vertex 
            (fun v ->
                P.print_info () "%s" "NODE: ";
                print_node v node_mappings;
                P.print_info () "%s" "SUCCS: ";
                List.iter 
                    (fun succ -> print_node succ node_mappings)
                    (G.succ g v);
                P.print_info () "%s\n" "=========")
            g
    
    let print_graph_info g node_mappings =
        if Param.info then
            print_graph g node_mappings
     
    let compare_nodes n1 n2 = 
        match (n1, n2) with
        | Statement s1, Statement s2 when s1.sid = s2.sid
            -> true
        | BeginCall (_, s1), BeginCall (_, s2) when s1.sid = s2.sid
            -> true
        | EndCall (_, s1), EndCall (_, s2) when s1.sid = s2.sid
            -> true
        | _ -> false   
    
    let get_node_stmt node =
        match node with
        | Statement s -> s
        | BeginCall (_, s) -> s
        | EndCall (_, s) -> s
    
    let get_node_value g node_mappings v =
        let node = Hashtbl.find node_mappings v in
        match node with
        | Statement s -> Param.node_value s
        | BeginCall (_, s) -> Param.node_value s
        | _ -> Param.value_default

    let get_edge_value g node_mappings src dst =
        let node_src = Hashtbl.find node_mappings src in
        let node_dst = Hashtbl.find node_mappings dst in
        let src_stmt = 
            match node_src with
            | Statement s -> s
            | BeginCall (_, s) -> s
            | EndCall (_, s) -> s in
            match node_dst with
            | Statement dst_stmt -> 
                Param.edge_value src_stmt dst_stmt 
            | BeginCall (_, dst_stmt) -> 
                Param.edge_value src_stmt dst_stmt
            | EndCall _ ->
                Param.value_default
                                                                            
    let do_add_edge g node_mappings src dest  =
        G.add_edge_e g (G.E.create src (get_edge_value g node_mappings src dest) dest)

    let create_graph funcs =
        let g = G.create () in
        let do_create_metric_node stmt =
            P.print_debug () "[DEBUG][NODES] Adding node for stmt sid: %d\n" stmt.sid;
            match stmt.skind with
            | Instr (Call (_, call_exp, _, _)) -> 
                let finfo = Utils.get_lval_vinfo (Utils.extract_lvalue_from_expr call_exp) in
                let callee = Hashtbl.find Param.func_hash finfo.vname in
                [BeginCall (callee, stmt);
                 EndCall (callee, stmt)]
            | _ ->
                [Statement stmt]
        in
        let do_add_func_graph_nodes node_mappings_ref vertex_mappings_ref func =
            List.iter
                (fun stmt ->
                    let metric_nodes = do_create_metric_node stmt in  
                    List.iter 
                        (fun metric_node -> 
		                    let v = G.V.create metric_node in
		                    G.add_vertex g v;
		                    Hashtbl.add !node_mappings_ref v metric_node;
                            Hashtbl.add !vertex_mappings_ref metric_node v)
                        metric_nodes)
                func.sallstmts
        in
        let do_add_edges node_mappings vertex_mappings =
            let do_find_dest_vertexes sid =
                let results = ref [] in
                Hashtbl.iter
                    (fun node_type v ->
                        match node_type with
                        | Statement stmt -> if stmt.sid = sid then results := v::!results
                        | BeginCall (_, stmt) -> if stmt.sid = sid then results := v::!results
                        | _ -> ignore ())
                    vertex_mappings;
                !results
            in
            let do_find_end_call_vertex sid =
                let result = ref None in
                Hashtbl.iter
                    (fun node_type v ->
                        match node_type with
                        | EndCall (_, stmt) -> if stmt.sid = sid then result := Some v
                        | _ -> ignore ())
                    vertex_mappings;
                match !result with
                | None -> failwith "[ERROR][METRICS_GRAPH] Unable to find EndCall node."
                | Some v -> v 
            in
            let do_find_pred_vertexes funcdec =
                let results = ref [] in
                List.iter
                    (fun stmt -> 
                        if List.length stmt.succs = 0 then 
                            Hashtbl.iter
                                (fun node_type v ->
                                    match node_type with
                                    | Statement s -> if stmt.sid = s.sid then results := v::!results
                                    | EndCall (_, s) -> if stmt.sid = s.sid then results := v::!results
                                    | _ -> ignore ())
                            vertex_mappings)
                    funcdec.sallstmts;
                !results
            in
            let do_find_succ_vertexes stmt =
                let results = ref [] in
                List.iter
                    (fun succ_stmt ->
                        Hashtbl.iter
                            (fun node_type v ->
                                match node_type with
                                | Statement s -> if succ_stmt.sid = s.sid then results := v::!results
                                | BeginCall (_, s) -> if succ_stmt.sid = s.sid then results := v::!results
                                | _ -> ignore ())
                            vertex_mappings)
                    stmt.succs;
                !results
            in
            
            Hashtbl.iter 
                (fun v metric_node ->
                    match metric_node with
                    | Statement stmt ->
                        List.iter
                            (fun succ_stmt ->
                                let succ_vertexes = do_find_dest_vertexes succ_stmt.sid in
                                List.iter
                                    (fun succ_v -> 
                                        do_add_edge g node_mappings v succ_v)
                                succ_vertexes)
                            stmt.succs;
                    | BeginCall (funcdec, stmt) ->
                        (match funcdec.sallstmts with
                        | [] ->
                            let end_call_v = do_find_end_call_vertex stmt.sid in
                            do_add_edge g node_mappings v end_call_v
                        | first::_ ->
                            let succ_vertexes = do_find_dest_vertexes first.sid in
                            List.iter
                                    (fun succ_v -> do_add_edge g node_mappings v succ_v)
                                succ_vertexes) 
                    | EndCall (funcdec, stmt) ->
                        let pred_vertexes = do_find_pred_vertexes funcdec in
                        List.iter (fun pred_v -> do_add_edge g node_mappings pred_v v) pred_vertexes;
                        let succ_vertexes = do_find_succ_vertexes stmt in
                        List.iter (fun succ_v -> do_add_edge g node_mappings v succ_v) succ_vertexes)
                node_mappings
        in
        
        let node_mappings = Hashtbl.create 1024 in
        let vertex_mappings = Hashtbl.create 1024 in
        List.iter
            (fun funcdec ->
                do_add_func_graph_nodes (ref node_mappings) (ref vertex_mappings) funcdec)
        funcs;
        P.print_info () "%s\n" "[INFO] Finished creating metrics graph nodes";
        do_add_edges node_mappings vertex_mappings;
        P.print_info () "%s\n" "[INFO] Finished creating metrics graph edges";
        print_graph_info g node_mappings;
        (g, node_mappings, vertex_mappings)
        
    let break_loops (g, node_mappings, vertex_mappings) =
        let do_get_entry_point scc =
            (* TODO: find better way to determine entry point *)
            let entry = ref (List.hd scc) in
            List.iter 
                (fun v ->
                    let preds = G.pred g v in
                    let cnt = List.fold_left 
                        (fun cnt p ->
                            if List.mem p scc then
                                cnt + 1
                            else
                                cnt)
                        0
                        preds in
                    if cnt > 0 then entry := v)
                scc;
            P.print_info () "%s\n" "Entry node :";
            print_node_info !entry node_mappings;
            !entry
        in
        let do_get_loop_edge scc =
            let visited = Hashtbl.create 1024 in
            let back_edge = ref None in
            let rec df vertex =
                if !back_edge = None then 
	                (Hashtbl.add visited vertex true;
	                let succs = G.succ g vertex in
	                List.iter 
	                    (fun succ ->
	                        if Hashtbl.mem visited succ then 
	                            back_edge := Some (vertex, succ)
	                        else if List.mem succ scc then
	                            df succ)
                        succs)
            in
            
            let entry_point = do_get_entry_point scc in
            df entry_point;
            match !back_edge with
            | None -> 
                P.print_info () "%s\n" "[INFO] Didn't find any back edge";
                None
            | Some (vertex, succ) -> 
                P.print_info () "%s\n" "[INFO] Found back edge";
                Some (vertex, succ)
        in
        let removed_edges_ref = ref [] in
        let has_loops = ref true in
        let v_count = G.nb_vertex g in
        while !has_loops do
            let sccs = SCC.scc_list g in
            print_sccs_info sccs node_mappings;
            if List.length sccs = v_count then (
                P.print_info () "%s\n" "[INFO] Graph doesn't have loops";
                has_loops := false
            ) else (
                P.print_info () "%s\n" "[INFO] Graph still has loops";
	            List.iter
	                (fun scc ->
                        match do_get_loop_edge scc with
                        | None -> ignore ()
                        | Some (start_removed_edge, end_removed_edge) ->  
                            P.print_info () "%s\n" "start edge:";
                            print_node_info start_removed_edge node_mappings;
                            P.print_info () "%s\n" "end edge:";
                            print_node_info end_removed_edge node_mappings;
		                    G.remove_edge g start_removed_edge end_removed_edge;
	                        removed_edges_ref := 
                                (start_removed_edge, end_removed_edge)::!removed_edges_ref;
	                    )
                    sccs
            )
        done;
        P.print_info () "%s\n" "[INFO] Finished breaking loops in metrics graph";
        P.print_info () "%s\n" "[INFO] Removed edges: ";
        List.iter 
            (fun (start, stop) ->
                P.print_info () "%s\n" "[INFO] EDGE";
                print_node_info start node_mappings;
                print_node_info stop node_mappings)
            !removed_edges_ref;
        ((g, node_mappings, vertex_mappings), !removed_edges_ref)
        
    let get_best_path (g, node_mappings, vertex_mappings) start_stmt end_stmt =
        let start_ref = ref None in
        let end_ref = ref None in
        Hashtbl.iter
            (fun node v ->
                match node with
                | Statement s ->
                    if s.sid = start_stmt.sid then start_ref := Some v;
                    if s.sid = end_stmt.sid then end_ref := Some v
                | BeginCall (_, s) ->
                    if s.sid = start_stmt.sid then start_ref := Some v;
                    if s.sid = end_stmt.sid then end_ref := Some v
                | _ -> ignore ())
            vertex_mappings;
        let start_v = 
            match !start_ref with
	        | None -> failwith "[ERROR][SHORTEST PATH] Invalid start statement"
	        | Some v -> v in
        let end_v = 
            match !end_ref with
            | None -> failwith "[ERROR][SHORTEST PATH] Invalid end statement"
            | Some v -> v in 
        P.print_info () 
            "[INFO] Computing shortest path between sid %d and sid %d:\n" 
            start_stmt.sid 
            end_stmt.sid;
        let (shortest_path, weight) = Dij.shortest_path g start_v end_v in
        let weight = ref weight in
        let path_list = ref [] in
        List.iter 
            (fun e -> 
				let src = G.E.src e in
                print_node_info src node_mappings;
                path_list := src::!path_list)
            shortest_path;
        if List.length shortest_path > 0 then (
            let last = List.hd (List.rev shortest_path) in
            let dst = G.E.dst last in
            print_node_info dst node_mappings;
            path_list := dst::!path_list
        );
        (!path_list, !weight)
    
    let add_removed_edges (g, node_mappings, vertex_mappings) shortest_path weight removed_edges =
        let is_in_list lst v =
            let found = ref false in
            let node = Hashtbl.find node_mappings v in
            List.iter 
                (fun pv ->
                    if !found = false then
                        let path_node = Hashtbl.find node_mappings pv in
                        found := compare_nodes node path_node)
                shortest_path;
            !found
        in
        let is_loop_scc scc =
            let found = ref false in
            List.iter 
                (fun loop_v ->
                    if !found = false then
                        let loop_node = Hashtbl.find node_mappings loop_v in
                        found := 
                            List.exists
                                (fun (s, e) ->
                                    let s_node = Hashtbl.find node_mappings s in
                                    let e_node = Hashtbl.find node_mappings e in
                                    if compare_nodes loop_node s_node || 
                                        compare_nodes loop_node e_node then
                                        true
                                    else
                                        false)
                                removed_edges)
                scc;
            !found                  
        in
        
        (* TODO: remove recomputing the SCCs. They should be somehow stored. *)
        P.print_info () "%s\n" "[INFO] Initial SP weight";
        let weight = ref weight in
        List.iter
            (fun (start, stop) 
                -> 
                    if is_in_list shortest_path start 
                        || is_in_list shortest_path stop then (
                            P.print_info () "%s\n" "[INFO] Adding removed edge:";
                            print_node_info start node_mappings;
                            print_node_info stop node_mappings;
                            do_add_edge g node_mappings start stop
                        ))
            removed_edges;
        let sccs = SCC.scc_list g in
        let new_nodes = ref [] in
        List.iter
            (fun scc -> 
                if is_loop_scc scc then (
                    P.print_info () "%s\n" "[INFO] Found new SCC";
                    List.iter 
                    (fun loop_v ->
                        let loop_v_value = (get_node_value g node_mappings loop_v) in
                        if is_in_list shortest_path loop_v then (
                            P.print_info () "%s\n" "[INFO] Substracting current weight";
                            weight := Param.value_sub !weight loop_v_value
                        ) else if is_in_list !new_nodes loop_v = false then (
                            P.print_info () "%s\n" "[INFO] Loop node is new";
                            new_nodes := loop_v :: !new_nodes
                        );
                        weight := Param.value_add_second_in_loop !weight loop_v_value)
                    scc)
                )
            sccs;
        let stmt_hash = ref (Inthash.create 1024) in
        List.iter
            (fun v -> 
                let stmt = get_node_stmt (Hashtbl.find node_mappings v) in
                Inthash.add !stmt_hash stmt.sid stmt)
        (List.append shortest_path !new_nodes);
        (!stmt_hash, !weight)
end 
