open TaintGamma
open Utils
open Cil_types

(* Typing rules *)
module Typing (Param:sig
                    val fmt : Format.formatter
                    val debug : bool      
                    val info : bool     
                 end)=struct
    
    module TG = TypeHelper.TypeGetter(struct 
                            let fmt = Param.fmt
                            let debug = Param.debug
                            let info = Param.debug
                            end)
    
    module P = TaintPrinter.Printer(struct
                                        let fmt = Param.fmt
                                        let debug = Param.debug
                                        let info = Param.info
                                    end)
    
    (* Applies the oplus operator between taint values. *)
    let combine_taint t1 t2 =
        let taint_comparator g1 g2 =
            g1.vid = g2.vid
        in
        match (t1, t2) with
            | (T, _) 
            | (_, T) -> T
            | ((G g), U) -> (G g)
            | (U, (G g)) -> (G g)
            | (U, U) -> U
            | ((G g1), (G g2)) -> (G (reunite taint_comparator g1 g2))
    
    let combine_taint_list taint_list =
        List.fold_left
            (fun t (_, taint) -> combine_taint t taint)
            U
            taint_list
            
    let add_to_taint_list (sid, t) l =
        match List.filter (fun (id, _) -> id == sid) l with
            | [] -> (sid, t)::l
            | _ -> l
    
    (* Combines two environments. Stores the result in the first parameter and *)
    (* returns it. *)
    let combine (vis1, _env1) (vis2, _env2) =
        let order_visited_first (v1, e1) (v2, e2) =
            match v1 with 
                | true -> ((v1, e1), (v2, e2))
                | false -> ((v2, e2), (v1, e1))
        in
        
        let ((vis1, _env1), (vis2, _env2)) = 
            order_visited_first (vis1, _env1) (vis2, _env2) in
        (* if one of the envs wasn't visited, the data there isn't sane so we*)
        (* ignore it :) *)
        match vis2 with
            | false -> 
                (true, _env1)
            | true ->
                Hashtbl.iter
                    (fun id t1 ->
                        let t2 = Hashtbl.find _env2 id in
                        Gamma.set_taint (vis1, _env1) id (combine_taint t1 t2)
                    )
                    _env1;
                (true, _env1)
    
    let visit_env (_, env) = (true, env)
    
    let instantiate_func_env env_hash taint_instances =
        let _find_instance vinfo =
            match 
                List.fold_left 
                    (fun i (vinfo_instance, taint) ->
                        match i with
                        | Some _ -> i
                        | None ->
                            if vinfo_instance.vid == vinfo.vid then
                                Some taint
                            else
                                None)
                    None
                    taint_instances with
            | None -> 
                P.print () "%s\n" "[ERROR] INSTANTIATE_FUNC_ENV ERROR";
                T
            | Some t -> t
        in
        let _instantiate_taint taint =
            match taint with
                | T -> T
                | U -> U
                | G g_list ->
                    List.fold_left
                        (fun t g ->
                            combine_taint t (_find_instance g))
                        U
                        g_list
        in
        let _instantiate_env env =
            let new_env = Gamma.create_env () in
            Gamma.env_iter
                (fun id taint ->
                    let taint_instance = _instantiate_taint taint in
                    Gamma.set_taint new_env id taint_instance)
                env;
            new_env
        in
        
        let instance_env_hash = Inthash.create 1024 in
        Inthash.iter
            (fun id env ->
                let new_env = _instantiate_env env in
                Inthash.add instance_env_hash id new_env)
            env_hash;
        instance_env_hash
    
    (* Locals are initialized to tainted. An exception is made for structures. *)
    (* All structures are initialized to untainted because only parts of the *)
    (* structures may be used afterwards. *)
    let process_local env vinfo =
        Gamma.set_taint env vinfo.vid U;
        env
    
    (* Formals are initialized to G. *)
    let process_formal env vinfo =
        let t = (G [vinfo]) in 
        Gamma.set_taint env vinfo.vid t;
        env
        
    let process_global env vinfo = 
        Gamma.set_taint env vinfo.vid (G [vinfo]);
        env
    
    let process_function_return env vinfo taint =
        Gamma.set_taint env (-vinfo.vid) taint;
        env
    
    let get_function_return_vid vinfo =
        - vinfo.vid
end
