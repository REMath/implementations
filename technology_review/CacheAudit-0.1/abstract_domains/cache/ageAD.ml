(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)



open Big_int
open AD.DS
open NumAD.DS

module type S = sig
  include AD.S
  val init : int -> (var -> int) -> (var->string) -> t
  val inc_var : t -> var -> t
  val set_var : t -> var -> int -> t
  val delete_var : t -> var -> t
  val permute : t -> (int -> int) -> var -> t
  val get_values : t -> var -> int list
  val exact_val : t -> var -> int -> (t add_bottom)
  val comp : t -> var -> var -> (t add_bottom)*(t add_bottom)
  val comp_with_val : t -> var -> int -> (t add_bottom)*(t add_bottom)
  val count_cstates: t -> big_int * big_int
end


module Make (V: NumAD.S) = struct
  
  type t = {
    value: V.t;
    max_age : int; (*all values bigger than max_age are assumed to be max_age *)
    pfn : var -> int;
  }
    
  
  let init max_age pfn v2s = {
    value = V.init v2s; 
    max_age = max_age;
    pfn = pfn;
  }

  let join e1 e2 = 
    assert (e1.max_age = e2.max_age);
    {e1 with value = (V.join e1.value e2.value)}
  
  let flatten (d1,d2,d3,d4) =
    let result = List.fold_left (lift_combine V.join) Bot [d1;d2;d3;d4] in
    match result with
      Bot -> failwith "SValAD.flatten: bottom"
    | Nb a -> a

  (* computes comparison of x1 and x2, see vguard below *)
  (* the first result is x1<x2, the second one x1=x2 and the last one x1>x2 *)
  let vcomp venv x1 x2 =
   let _,tf,ft,ff= V.flagop venv X86Types.Sub x1 x2 in
    (* Since we only have positive values, when the carry flag is set, it means venv is strictly smaller than x2 *)
    (* The case where there is a carry and the result is zero should not be 
possible, so it approximates Bottom *)
   tf,ft,ff

  (* Compute x<c in V, where x is a variable and c an int. Should be extended to the case where c is a var *)
  (* the first result is x<c, the second one x=c and the last one x>c *)
  let vguard venv x c = vcomp venv (VarOp x) (Cons(Int64.of_int c))

  let inc_var env v = 
    let young,nyoung,_ = vguard env.value v env.max_age in
(* we assume the cases bigger than max_age are irrelevent and we never increase values above max_age *)
    let new_valad = 
      match young with
      | Bot -> env.value
      | Nb yenv ->
        let yenv = flatten (V.update_var yenv v NoMask (Cons 1L) NoMask (AbstractInstr.Op X86Types.Add)) in
        match nyoung with
        | Bot -> yenv
        | Nb nyenv -> V.join yenv nyenv
    in {env with value = new_valad}
                       
  let is_var env a = V.is_var env.value a

  let set_var env v a = 
      if a > env.max_age then
        failwith "simpleValAD: set_var cannot set to values greater than the maximal value"
      else
        let value = if not (is_var env v) then 
                    V.new_var env.value v
                  else env.value
        in let value = flatten(V.update_var value v NoMask (Cons(Int64.of_int a)) NoMask AbstractInstr.Move) in
        {env with value = value}
  
  
  let list_max l = List.fold_left (fun m x -> if x > m then x else m ) 0L l
 
  (* updates an env according to the value env *)
  let vNewEnv env = function
    Bot -> Bot
  | Nb venv -> Nb{env with value = venv}

  (* the first result is approximates the cases when x1 < x2 and
     the second one when x1 > x2 *)
  let comp env x1 x2 = 
    let smaller, _, bigger = vcomp env.value (VarOp x1) (VarOp x2) in
    vNewEnv env smaller, vNewEnv env bigger

  let comp_with_val env x v =
    let smaller, eq, bigger = vguard env.value x v in
    vNewEnv env smaller, lift_combine join (vNewEnv env eq) (vNewEnv env bigger)

  let exact_val env x c =
    let smaller, eq, bigger = vguard env.value x c in vNewEnv env eq

  (* apply the permutation perm to the age of variable x *)
  let permute env perm x = 
    let perm64 a = Int64.of_int (perm (Int64.to_int a)) in
    match V.get_var env.value x with
      Tp -> env
    | Nt vm -> 
      let v1,_ = NumMap.min_binding vm in
      let value1 = let nv1 = perm64 v1 in V.set_var env.value x nv1 nv1 in 
      {env with value = 
           NumMap.fold (fun c _ value -> let nc = perm64 c in
                        V.join value (V.set_var value x nc nc))
                     (NumMap.remove v1 vm) value1
      }
  
  let print_delta env1 fmt env2 = V.print_delta env1.value fmt env2.value
  let print fmt env = V.print fmt env.value
  let subseteq env1 env2= 
    assert (env1.max_age = env2.max_age);
    (V.subseteq env1.value env2.value)
  let widen env1 env2 = 
    assert (env1.max_age = env2.max_age);
    {env1 with value = (V.widen env1.value env2.value)}

  let get_values env v = let l = match V.get_var env.value v with
     Tp -> []  | Nt x -> NumMap.bindings x in
     List.map (fun (k,v) -> Int64.to_int k) l
  
  let delete_var env v = {env with value = V.delete_var env.value v}
    
  
  (*** Counting valid states ***)
  
  (* Checks if the given cache state is valid *)
  (* with respect to the ages defined in cache.ages. *)
  let is_valid_cstate env addr_set cache_state  = 
    let rec pos addr l i = match l with 
       [] -> env.max_age
    | hd::tl -> if hd = addr then i else pos addr tl (i+1) in
    NumSet.for_all (fun addr -> 
      List.mem (pos addr cache_state 0)(get_values env addr)) addr_set 
  
  (* Count the number of n-permutations of the address set addr_set *)
  let num_tuples env n addr_set = 
    if NumSet.cardinal addr_set >= n then begin
      let rec loop n elements tuple s = 
        if n = 0 then begin
          if is_valid_cstate env addr_set tuple then Int64.add s 1L else s
        end else
          NumSet.fold (fun addr s -> 
            loop (n-1) (NumSet.remove addr elements) (addr::tuple) s) 
            elements s in 
        loop n addr_set [] 0L
    end else 0L
    
  (* Computes two lists list where each item i is the number of possible *)
  (* cache states of cache set i for a shared-memory *)
  (* and the disjoint-memory (blurred) adversary *)
  let cache_states_per_set env =
    let cache_sets = Utils.partition (V.var_names env.value) env.pfn in
    IntMap.fold (fun _ addr_set (nums,bl_nums) ->
      let num_tpls,num_bl =
        let rec loop i (num,num_blurred) =
          if i > env.max_age then (num,num_blurred)
          else
            let this_num = 
              num_tuples env i addr_set in 
            let this_bl = if this_num > 0L then 1L else 0L in
            loop (i+1) (Int64.add num this_num, Int64.add num_blurred this_bl)
         in loop 0 (0L,0L) in
      (num_tpls::nums,num_bl::bl_nums)) cache_sets ([],[])
      
  let count_cstates env = 
    let nums_cstates,bl_nums_cstates = cache_states_per_set env in
      (Utils.prod nums_cstates,Utils.prod bl_nums_cstates)
end

