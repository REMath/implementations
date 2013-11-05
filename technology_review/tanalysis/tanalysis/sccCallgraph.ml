open Cil_types
open Cilutil
open Cil
open Graph
open Callgraph

type 'a funcNodeType = FuncNone 
                    | FuncNonRecursive of ('a * 'a list) 
                    | FuncRecursive of 'a list

module FunctionsComputer = struct 
 
    module G = Imperative.Digraph.Abstract(struct type t = callnode end)
    
    module SCC = Components.Make(G)

    let create_graph call_graph =
        let g = G.create () in        
        let (mappings, nodes) = 
            Hashtbl.fold
                (fun key cn (result_m, result_n) ->
                    let v = G.V.create cn in
                    G.add_vertex g v;
                    Hashtbl.add result_n (nodeName cn.cnInfo) v;
                    Hashtbl.add result_m v cn;
                    (result_m, result_n))    
            call_graph 
            (Hashtbl.create 512, Hashtbl.create 512) in
        Hashtbl.iter
            (fun key cn ->
                let name = nodeName cn.cnInfo in
                let n1 = Hashtbl.find nodes name in
                Inthash.iter
                    (fun key cn_callee ->
                        let callee = nodeName cn_callee.cnInfo in
                        let n2 = Hashtbl.find nodes callee in
                        G.add_edge g n1 n2
                        )
                    cn.cnCallees
            ) call_graph;
        (mappings, nodes, g)
        
    let compute_scc call_graph =
        let (mappings, nodes, g) = create_graph call_graph in
        let array = SCC.scc_array g in
        let lst = Array.to_list array in
        (mappings, nodes, g, lst)
                               
end

let get_next_call mappings nodes g l =
    let list_contains cnode =
        let name = nodeName cnode.cnInfo in
        let result = List.fold_left 
            (fun found el ->
                match found with
                    | true -> true
                    | false ->
                        let cnode = Hashtbl.find mappings el in
                        let cnode_name = nodeName cnode.cnInfo in
                        name == cnode_name)
            false
            l in
        result
    in 
    let calls_in_list cnode =
        Inthash.fold 
            (fun key callee_node found ->
                found || list_contains callee_node)
            cnode.cnCallees
            false
    in
    match List.length l with
        | 0 -> FuncNone
        | _ -> 
            try
                let ret_node = 
                    List.find
                        (fun node ->
                            let call_node = Hashtbl.find mappings node in
                            let calls = calls_in_list call_node in
                            match calls with
                                | true -> false
                                | false -> true)
                         l in
                FuncNonRecursive (ret_node, List.filter (fun n -> n != ret_node) l)
            with Not_found 
                ->
                    FuncRecursive l

let get_scc () =
    let module FC = FunctionsComputer in
    let cg = computeGraph (Cil_state.file ()) in
    let (mappings, nodes, g, lst) = FC.compute_scc cg in
    (mappings, nodes, g, lst)
