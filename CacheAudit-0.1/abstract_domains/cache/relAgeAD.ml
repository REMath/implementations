(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)

open Printf
open RelAgeFnSet
open RelSetMap
open AD.DS
open NumAD.DS
open Logger

module type S = AgeAD.S

module RelAgeAD = struct
  module M = RelSetMap
  type t = {
    map : M.t;
    arity : int; 
    max : int;
    pfn : var -> int;
  }

  let debug = ref false

  (* partition helper *)
  let rec add_to_setlist (setlist:NumSet.t list) (vset:NumSet.t) : NumSet.t list = 
    match setlist with 
      hd::tl -> if NumSet.exists (fun v -> NumSet.mem v hd) vset then 
                add_to_setlist tl (NumSet.union vset hd) else
                hd::add_to_setlist tl vset
    | []     -> [vset]

  let partition rsAD = 
    let tmp = List.fold_left (fun setlist vset -> add_to_setlist setlist vset) [] (M.keys rsAD.map)  in
    List.fold_left (fun result vset -> NumSet.elements vset::result) [] tmp

  let init max pfn v2s = 
    {map = M.init_with_max v2s max; arity = 2; max = max; pfn = pfn}

  let get_values (rsAD:t) (v:var) : int list = 
    let vset = NumSet.add v NumSet.empty in
    AFS.values (M.find vset rsAD.map) v

  let mem (rsAD:t) (part_state:(var * int) list) : bool = 
    M.for_all (fun vset afs -> not (AFS.contradicts afs part_state)) rsAD.map
    
  let forget_rel_info map (v:var) = 
    M.filter (fun vset _ -> not (NumSet.mem v vset)) map

  exception NotImplemented
  let is_var env a = raise NotImplemented
  
  let set_var (rsAD:t) (v:var) (age:int) = 
    let map = forget_rel_info rsAD.map v in
    let vset = NumSet.add v NumSet.empty in
    {rsAD with map = M.add vset (AFS.singleton v age) map}

  let inc_var (rsAD:t) (v:var) =
    {rsAD with map = M.mapi (fun vset afs -> if NumSet.mem v vset then AFS.inc_var afs v rsAD.max else afs) rsAD.map}
  
  let print (fmt:Format.formatter) (rsAD:t) = M.print fmt rsAD.map

  let print_delta (rsAD1:t) (fmt:Format.formatter) (rsAD2:t) = M.print_delta rsAD1.map fmt rsAD2.map 

  let join (rsAD1:t) (rsAD2:t) : t = 
    (* Determine all NumSets which have different Age Function Sets. *)
    let diffs = M.differences rsAD1.map rsAD2.map in
    let new_map = List.fold_left (fun map (vset,afs1,afs2) -> 
      let joined_afs = AFS.join afs1 afs2 in
      M.add vset joined_afs map
      ) rsAD1.map diffs in
    (* Add relational Information where we can gain precision *)
    let new_map = List.fold_left 
      (
       fun map (vset,afs1,afs2) -> List.fold_left 
         (
          fun map' (vset',afs1',afs2') -> 
            let comb_vset = NumSet.union vset vset' in 
            if M.mem comb_vset map' || NumSet.cardinal comb_vset > rsAD1.arity then 
              map' 
            else
             let comb_afs1 = AFS.combine afs1 afs1' in
             let comb_afs2 = AFS.combine afs2 afs2' in
             M.add comb_vset (AFS.join comb_afs1 comb_afs2) map'
         ) map diffs
       ) new_map diffs in 
    {rsAD1 with map = new_map}

  let widen (rsAD1:t) (rsAD2:t) : t = join rsAD1 rsAD2

  let subseteq (rsAD1:t) (rsAD2:t) : bool = 
    M.for_all (fun vset afs1 -> AFS.subseteq afs1 (M.find vset rsAD2.map)) rsAD1.map

  (* Check if no Relation is empty, i.e. there is no valid position for some variable (combination) *)
  let check_validity rsAD = if M.for_all (fun k set -> not (AFS.is_empty set)) rsAD.map then Nb rsAD else Bot 

  let comp (rsAD:t) (v1:var) (v2:var) : (t add_bottom)*(t add_bottom) = 
    let v2_vals = AFS.values (M.find (NumSet.add v2 NumSet.empty) rsAD.map) v2 in 
    let sm_v2 = List.hd (List.sort Pervasives.compare v2_vals) in
    let gt_v2 = List.hd (List.sort (fun x y -> Pervasives.compare y x) v2_vals) in

    let subrelations (name:NumSet.t) : NumSet.t list = NumSet.fold (fun v l -> NumSet.remove v name::l) name [] in

    (* Extends the relation by variable v and insures that all subrelations are fulfilled. *)
    let extend_relation (name:NumSet.t) (v:var) (map:M.t) : AFS.t = 
       let old_set = M.find name map in 
       let v_set = M.find (NumSet.add v NumSet.empty) map in 
       let new_set = AFS.combine old_set v_set in
       (* Filter out ages violating subrelations *)
       let new_set = List.fold_left (fun age_set name_sub -> AFS.filter age_set (M.find name_sub map)) new_set (subrelations (NumSet.add v name)) in 
      new_set in

    (* Removes v from the relation. *)
    let shrink_relation (v:var) (ages:AFS.t) : AFS.t = 
      let vars = NumSet.remove v (AFS.vset ages) in
      AFS.project ages (NumSet.elements vars) in

    let update_ages (vset:NumSet.t) map (compare:int->int->int) (limit:int): AFS.t  = 
      let old_ages = M.find vset map in 
      match NumSet.mem v1 vset, NumSet.mem v2 vset with  
          true , true  -> AFS.filter_comp old_ages v1 v2 compare (* compare v1 v2 = -1*)
        | true , false -> let ext_ages = extend_relation vset v2 rsAD.map in
              let ext_ages = AFS.filter_comp ext_ages v1 v2 compare in
              shrink_relation v2 ext_ages
        | false, true  -> old_ages
        | false, false -> old_ages in 
    let ls  = M.mapi (fun vset afs -> update_ages vset rsAD.map Pervasives.compare gt_v2) rsAD.map in
    let gt = M.mapi (fun vset afs -> update_ages vset rsAD.map (fun x y -> Pervasives.compare y x) sm_v2) rsAD.map in 
    (check_validity {rsAD with map = ls},check_validity {rsAD with map = gt})

  let comp_with_val rsAD v1 c = 
    let update_ages (vset:NumSet.t) map (compare:int->int->int) (limit:int): AFS.t  = 
      let old_ages = M.find vset map in 
      match NumSet.mem v1 vset with  
          true   -> AFS.filter_comp_val old_ages v1 limit compare
        | false -> old_ages in 
    let ls  = M.mapi (fun vset afs -> update_ages vset rsAD.map Pervasives.compare c) rsAD.map in
    let gt = M.mapi (fun vset afs -> update_ages vset rsAD.map (fun x y -> Pervasives.compare y x) c) rsAD.map in 
    (check_validity {rsAD with map = ls},check_validity {rsAD with map = gt})

  let exact_val rsAD v c = failwith "exact_val (needed for PLRU) not yet implem
ented in relational sets" (*TODO*)

  let permute rsAD f v = failwith "permute (needed for PLRU) not yet implemente
d in relational sets" (*TODO*)

  let delete_var env v = failwith "relAgeAD: remove not implemented yet"


  (*** Counting valid states ***)
  
    (*partition helper *)
  let rec add_to_setlist setlist set  =     match setlist with 
      hd::tl -> if IntSet.exists (fun v -> IntSet.mem v hd) set then 
                add_to_setlist tl (IntSet.union set hd) else
                hd::add_to_setlist tl set
    | []     -> [set]

  let merge_sets (unmerged_sets:IntSet.t list) : IntSet.t list  = 
    List.fold_left (fun merged_sets set -> add_to_setlist merged_sets set) [] unmerged_sets
  

  type af = (var*int) list

(* replace the element at position n in the list l with element e *)
  let rec list_replace (n:int) (l: 'a list) (e: 'a) : 'a list = 
    match n with 0 -> e :: (List.tl l) | m -> List.hd l :: list_replace (n-1) (List.tl l) e

  let satisfies_cache_constraints env (state:af) (inv_cachemap) : bool = 
    (* Split list s.t. we get 1 list per cache set*)
    let split_state : (int * af) list = 
       let rec insert ((v,i):var * int) (l:(int * af) list) = 
         if i = env.max then l else (* dont insert blocks which are not in the cache *)
         match l with 
           [] -> [(NumMap.find v inv_cachemap ,[(v,i)])] 
         |(setnr,l')::tl -> if NumMap.find v inv_cachemap = setnr then 
                            (setnr,(v,i)::l')::tl else
                            (setnr,l')::insert (v,i) tl
       in
       List.fold_left (fun result (v,i) -> insert (v,i) result) [] state in
     (* Check constraints for each set *)
    let valid (state:af) :bool = 
       (* Compute occurrences of positions *)
       let rec helper n : int list = match n with 0 -> [] | x -> 0::helper (x-1) in
       let occurrences = List.fold_left (fun occ (v,i)-> 
        list_replace i occ ((List.nth occ i)+1)) 
        (helper env.max) (state) in
       (* Check if every position in the cache occurs only once and has a predecessor *)
       let rec check (l:int list) : bool = match l with
           [] -> true
         | hd::tl -> if hd = 0 then List.for_all (fun i -> i = 0) tl else (hd = 1) && check tl in 
       check occurrences in 
    List.for_all (fun (setnr,af) -> valid af) split_state

  let cache_states_of_partition env cache_sets (setnums:IntSet.t) : int = 
    (* invert cache map *)
    let inv_cachemap = IntMap.fold (fun setnum addrset map -> 
      NumSet.fold (fun addr map'-> NumMap.add addr setnum map')addrset map) 
      cache_sets NumMap.empty in
   (* function to compute the solutions of this partition *)
    let rec solutions v values unused current  = 
      match unused with 
         [] -> List.fold_left (fun result i -> if mem env ((v,i)::current) &&
           satisfies_cache_constraints env ((v,i)::current) inv_cachemap 
          then 1+result else result) 0 values
      | hd::tl -> let new_values = get_values env hd in
         List.fold_left (fun result i -> 
          if mem env ((v,i)::current) 
          then result + solutions hd new_values tl ((v,i)::current) 
          else result) 0 values
       in
    let all_addresses = IntMap.fold (fun num set result -> 
      if IntSet.mem num setnums then NumSet.union set result else result ) 
      cache_sets  NumSet.empty in
    match NumSet.elements all_addresses with 
    | [] -> 0 
    | hd::tl -> solutions hd (get_values env hd) tl []

  let comp_setnums env : IntSet.t list = let fmt = Format.std_formatter in
    (* Compute partitions induced by constraints *)
    let partitions = List.map (fun vlist -> List.fold_left 
      (fun result elem -> NumSet.add elem result) NumSet.empty vlist) (
        partition env) in
    (* convert variables to their respective set number *)
    let setnums = List.fold_left (fun newlist set -> 
      (NumSet.fold (fun addr intset -> 
        IntSet.add (env.pfn addr) intset) set IntSet.empty)::newlist)
        [] partitions in
    (* merge sets containing the same set numbers *)
    let result = merge_sets setnums in
    if !debug then
      Format.fprintf fmt "Partitioning leads to parts of size: (";
        List.iter (fun set -> Format.fprintf fmt " %d, " 
        (IntSet.cardinal set)) result; Format.fprintf fmt ") 
        cache sets\n";Format.print_flush ();
    result

  let count_cstates env =
    let elts = List.fold_left (fun elts set -> 
      NumSet.union elts set) NumSet.empty (M.keys env.map) in
    let cache_sets = Utils.partition elts env.pfn in
    let setnums = comp_setnums env in
    let states_per_part = 
      List.fold_left (fun l setnums -> 
        cache_states_of_partition env cache_sets setnums::l) [] setnums in
    let num = List.fold_left (fun sol set_sol -> 
      Int64.mul sol (Int64.of_int set_sol)) Int64.one states_per_part in
    let num = Big_int.big_int_of_int64 num in
    num,(Big_int.big_int_of_int (-1))

end
