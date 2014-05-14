(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)

open AD.DS
open NumAD.DS
open Logger

type cache_strategy = 
  | LRU  (** least-recently used *)
  | FIFO (** first in, first out *)
  | PLRU (** tree-based pseudo LRU *)
type cache_param = { 
  cs: int; 
  ls: int; 
  ass: int; 
  str: cache_strategy;
 } 

module type S = sig
  include AD.S
  val init : cache_param -> t
  (** initialize an empty cache
   takes arguments cache_size (in bytes), 
  line_size (in bytes) and associativity *)
  val touch : t -> int64 -> t
  (** reads or writes an address into cache *)

  (** Same as touch, but returns more precise informations about hit and misses *)
  (** @return, the first set overapproximates hit cases, the second one misses *)
  val touch_hm : t -> int64 -> (t add_bottom*t add_bottom)
  (** Used to keep track of time, if neccessary *)
  val elapse : t -> int -> t
  val count_cache_states : t -> Big_int.big_int
end




open Big_int 

let precise_touch = ref true

type adversay = Blurred | SharedSpace

let adversary = ref Blurred

(* Permutation to apply when touching an element of age a in PLRU *)
(* We assume an ordering correspond to the boolean encoding of the tree from *)
(* leaf to root (0 is the most recent, corresponding to all 0 bits is the path *)

let plru_permut assoc a n = if n=assoc then n else
  let rec f a n =  if a=0 then n 
    else if a land 1 = 1 then if n land 1 = 1 then 2*(f (a/2) (n/2)) else n+1
    else (* a even*) if n land 1 = 1 then n else 2*(f (a/2) (n/2))
  in f a n


module Make (A: AgeAD.S) = struct
  type t = {
    handled_addrs : NumSet.t; (* holds addresses handled so far *)
    cache_sets : NumSet.t IntMap.t;
    (* holds a set of addreses which fall into a cache set
        as implemented now it may also hold addresses evicted from the cache *)
    ages : A.t;
    (* for each accessed memory address holds its possible ages *)

    cache_size: int;
    line_size: int; (* same as "data block size" *)
    associativity: int;
    num_sets : int; (* computed from the previous three *)
    strategy : cache_strategy; 
  }

  let print_addr_set fmt = NumSet.iter (fun a -> Format.fprintf fmt "%Lx " a)


  let count_cache_states env = 
    let num_cstates,bl_num_cstates = A.count_cstates env.ages in
    match !adversary with
    | Blurred -> num_cstates
    | SharedSpace -> bl_num_cstates
  
  (* [print num] prints [num], which should be positive, as well as how many
     bits it is. If [num <= 0], print an error message *)
  let print_num fmt num =
    let strnum = string_of_big_int num in
    if gt_big_int num zero_big_int then 
      Format.fprintf fmt "%s, (%f bits)\n" strnum (Utils.log2 num)
    else begin
      Format.fprintf fmt "counting not possible\n";
      if get_log_level CacheLL = Debug then
        Format.fprintf fmt  "Number of configurations %s\n" strnum;
    end
  
  let print fmt env =
    if get_log_level CacheLL <> Quiet then begin 
      Format.fprintf fmt "@[<v 2>";
      IntMap.iter (fun i all_elts ->
          if not (NumSet.is_empty all_elts) then begin
            Format.fprintf fmt "@;@[ Set %4d: " i;
            NumSet.iter (fun elt -> Format.fprintf fmt "%Lx @," elt) all_elts;
            Format.fprintf fmt "@]"
          end
        ) env.cache_sets;
    end else ();
    Format.fprintf fmt "@.Possible ages of blocks:@; %a@]" A.print env.ages;
    if env.strategy = PLRU then 
      Format.fprintf fmt "Counting on PLRU is incorrect\n";
    Format.printf "\n";
    let num, bl_num = A.count_cstates env.ages in
    Format.fprintf fmt "\nNumber of valid cache configurations: ";
    print_num fmt num;
    Format.fprintf fmt "\nNumber of valid cache configurations (blurred): ";
    print_num fmt bl_num
  
  let var_to_string x = Printf.sprintf "%Lx" x 
  
  let calc_set_addr num_sets addr = 
    Int64.to_int (Int64.rem addr (Int64.of_int num_sets))

  (* Determine the set in which an address is cached *)
  let get_set_addr env addr =
    calc_set_addr env.num_sets addr
    
  let init cache_param =
    let (cs,ls,ass,strategy) = (cache_param.cs, cache_param.ls,
      cache_param.ass,cache_param.str) in
    let ns = cs / ls / ass in (* number of sets *)
    let rec init_csets csets i = match i with
    | 0 -> csets
    | n -> init_csets (IntMap.add (n - 1) NumSet.empty csets) (n - 1) in
    { cache_sets = init_csets IntMap.empty ns;
      ages = A.init ass (calc_set_addr ns) var_to_string;
      handled_addrs = NumSet.empty;
      cache_size = cs;
      line_size = ls;
      associativity = ass;
      num_sets = ns;
      strategy = strategy;
    }


  (* Gives the block address *)
  let get_block_addr env addr = Int64.div addr (Int64.of_int env.line_size)

  (* let get_keys map = let keys,_ = List.split (ValMap.bindings map) *)
  (*                    in List.map Int64.to_int keys                 *)
  (*                   (*TODO simplify this in Simple Values *)       *)

  (* Removes a cache line when we know it cannot be in the cache *)
  let remove_line env addr =
    let addr_set = get_set_addr env addr in
    let cset = IntMap.find addr_set env.cache_sets in
    let cset = NumSet.remove addr cset in
    { env with
      ages = A.delete_var env.ages addr;
      handled_addrs = NumSet.remove addr env.handled_addrs;
      cache_sets = IntMap.add addr_set cset env.cache_sets;
    } 


  let get_set_diffs aset1 aset2 =
     NumSet.diff aset1 aset2, NumSet.diff aset2 aset1

  let join c1 c2 =
    assert ((c1.associativity = c2.associativity) && 
      (c1.num_sets = c2.num_sets));
    let handled_addrs = NumSet.union c1.handled_addrs c2.handled_addrs in
    let cache_sets = IntMap.merge 
      (fun k x y ->
        match x,y with
        | Some cset1, Some cset2 ->
           Some (NumSet.union cset1 cset2)
        | Some cset1, None -> Some cset1
        | None, Some cset2 -> Some cset2
        | None, None -> None 
      ) c1.cache_sets c2.cache_sets in
    let assoc = c1.associativity in
    let haddr_1minus2,haddr_2minus1 =
      get_set_diffs c1.handled_addrs c2.handled_addrs in
    (* add missing variables to ages *)
    let ages1 = NumSet.fold (fun addr c_ages ->
      A.set_var c_ages addr assoc) haddr_2minus1 c1.ages in
    let ages2 = NumSet.fold (fun addr c_ages ->
      A.set_var c_ages addr assoc) haddr_1minus2 c2.ages in
    let ages = A.join ages1 ages2 in
    { c1 with ages = ages; handled_addrs = handled_addrs;
    cache_sets = cache_sets}

(* when addr is touched (and already in the cache set)
 update of the age of addr_in *)
(* In case where addr_in can be either older or younger than the intial age *)
(* of addr, splits the cases and returns two cache configurations *)
(* to allow some precision gain *)

  let age_one_element env addr addr_in =
    if addr = addr_in then env,None (*This case is treated later in touch*)
    else
      let young,nyoung = A.comp env.ages addr_in addr in
      match young with
      | Bot -> (match nyoung with
	(* This case is possible only if addr and addr_in have only maximal 
           age, i.e. if they are not loaded. TODO: sanity check here ? *)
        | Bot ->  remove_line env addr_in, None
        (* Age of blocks older than addr remains the same *)  
        | Nb nyenv -> { env with ages = nyenv }, None)
      | Nb yenv ->
         { env with ages = A.inc_var yenv addr_in },
           match nyoung with
             | Bot -> None
             | Nb nyenv -> Some {env with ages = nyenv }

  (* Increments the ages of all blocks that are in the same cache set as
     addr, which are given as a list of addresses *)
  let rec precise_age_elements env addr = function
    | [] -> env
    | addr_in :: clist -> (match age_one_element env addr addr_in with
      | new_env, None -> precise_age_elements new_env addr clist
      | env1, Some env2 ->
	let c1 = precise_age_elements env1 addr clist in
	let c2 = precise_age_elements env2 addr clist in
	(* TODO: see if it is too costly to remove some blocks here, as there *)
(*  could be some of them which need to be put back in the join *)
	join c1 c2)

  (*Increments all ages in the cache set [cset] by one *)           
  let incr_ages ages cset = match ages with 
    | Bot -> Bot
    | Nb ages -> Nb(NumSet.fold (fun addr_in a -> A.inc_var a addr_in) cset ages)
            
            
  let get_ages env addr = A.get_values env.ages (get_block_addr env addr)

(* returns the set of ages for addr_in that are different from the ages of addr *)
  let ages_different ages addr addr_in =
      let young,nyoung = A.comp ages addr_in addr in
      lift_combine A.join young nyoung
(* The effect of one touch of addr, restricting to the case when addr is of age c *)
  let one_plru_touch ages assoc cset addr c = 
    let ages_at_c = A.exact_val ages addr c in
    if c=assoc then incr_ages ages_at_c cset
    else match ages_at_c with Bot -> Bot
    | Nb ag -> (try 
        Nb(NumSet.fold (fun addr_in a -> if addr_in=addr then a
                else match ages_different a addr addr_in with
                  Bot -> raise Bottom
                | Nb a -> A.permute a (plru_permut assoc c) addr_in) cset ag )
      with Bottom -> Bot)

   (* adds a new address handled by the cache if it's not already handled *)
   (* We increment the age of all other adresses in the same set *)
   (* That works for LRU, FIFO and PLRU *)
   let add_new_address env addr set_addr cset =
      let ages = A.set_var env.ages addr 0 in
      let h_addrs = NumSet.add addr env.handled_addrs in
      (* increment the ages of elements in cache set *)
      (* also ages >= associativity are incremented; we may not want this *)
      let ages = NumSet.fold (fun addr oages -> A.inc_var oages addr) cset ages in
      let cache_sets = IntMap.add set_addr (NumSet.add addr cset) env.cache_sets in
      {env with ages = ages; handled_addrs = h_addrs; cache_sets = cache_sets}
  
  (* retuns true if addr was handled *)
  let is_handled env addr = 
    let set_addr = get_set_addr env addr in
    NumSet.mem addr (IntMap.find set_addr env.cache_sets)
  
  (* Reads or writes an address into cache *)
  let touch env orig_addr =
    if get_log_level CacheLL = Debug then Printf.printf "\nWriting cache %Lx" orig_addr;
    (* we cache the block address *)
    let addr = get_block_addr env orig_addr in
    if get_log_level CacheLL = Debug then Printf.printf " in block %Lx\n" addr;
    let set_addr = get_set_addr env addr in
    let cset = IntMap.find set_addr env.cache_sets in
    if is_handled env addr then begin
      let new_cache =
        match env.strategy with
        | LRU -> 
          let env = if !precise_touch 
          then precise_age_elements env addr (NumSet.elements cset)
          else NumSet.fold (fun addr_in curr_cache ->
      	    match age_one_element curr_cache addr addr_in with
      	      c, None -> c
      	    | c1, Some c2 -> (* in this case, only the ages differ *)
        		{c1 with ages = A.join c1.ages c2.ages}
        	  ) cset env
          in {env with ages = A.set_var env.ages addr 0}
        | FIFO -> (* We first split the cache ages in cases where addr is in the block and cases where it is not *)
          let ages_in, ages_out = 
            A.comp_with_val env.ages addr env.associativity in
          let env1 = match ages_in with Bot -> Bot
            | Nb ages_in -> Nb {env with ages=ages_in} (*nothing changes in that case *)
          and env2 = (*in this case we increment the age of all blocks in the set *)
            match incr_ages ages_out cset with Bot -> Bot
            | Nb ages -> Nb {env with ages=A.set_var ages addr 0}
          in (match lift_combine join env1 env2 with 
            Bot -> failwith "Unxepected bottom in touch when the strategy is FIFO"
          | Nb c -> c)
        | PLRU -> (* for each possible age of the block, we apply a different permutation *)
          let addr_ages = A.get_values env.ages addr in
          let ages = List.fold_left 
            (fun ages addr_age -> 
              lift_combine A.join ages 
                (one_plru_touch env.ages env.associativity cset addr addr_age)
            ) Bot addr_ages in
          (match ages with 
            Bot -> failwith "Unxepected bottom in touch when the strategy is PLRU"
          | Nb ages -> {env with ages = A.set_var ages addr 0}
          )
      (* in {new_cache with traces = traces} *)
      in new_cache
    end else add_new_address env addr set_addr cset 

  (* Same as touch, but returns two possible configurations, one for the hit and the second for the misses *)
  (* TODO: we could be more efficient here, by not calling touch, but modifying touch instead *)
  let touch_hm env orig_addr = 
    let addr = get_block_addr env orig_addr in 
    let set_addr = get_set_addr env addr in
    let cset = IntMap.find set_addr env.cache_sets in
    if is_handled env addr  then begin
      (* ages_in is the set of ages for which there is a hit *)
      let ages_in, ages_out = 
          A.comp_with_val env.ages addr env.associativity in
      let t a = match a with Bot -> Bot 
                | Nb a -> Nb(touch {env with ages=a} orig_addr)
      in
      (t ages_in, t ages_out)
    end else (Bot, Nb(add_new_address env addr set_addr cset))



  let widen c1 c2 = 
    join c1 c2

  let subseteq c1 c2 =
    assert 
      ((c1.associativity = c2.associativity) && (c1.num_sets = c2.num_sets));
    (NumSet.subset c1.handled_addrs c2.handled_addrs) &&
    (A.subseteq c1.ages c2.ages) &&
    (IntMap.for_all (fun addr vals ->
      if IntMap.mem addr c2.cache_sets
      then NumSet.subset vals (IntMap.find addr c2.cache_sets)
      else false
     ) c1.cache_sets)


  let print_delta c1 fmt c2 = match get_log_level CacheLL with
    | Debug->
          let added_blocks = NumSet.diff c2.handled_addrs c1.handled_addrs
          and removed_blocks = NumSet.diff c1.handled_addrs c2.handled_addrs in
          if not (NumSet.is_empty added_blocks) then Format.fprintf fmt
            "Blocks added to the cache: %a@;" print_addr_set added_blocks;
          if not (NumSet.is_empty removed_blocks) then Format.fprintf fmt
            "Blocks removed from the cache: %a@;" print_addr_set removed_blocks;
          if c1.ages != c2.ages then begin
            (* this is shallow equals - does it make sense? *)
            Format.fprintf fmt "@;@[<v 0>@[Old ages are %a@]"
              (A.print_delta c2.ages) c1.ages;
            (* print fmt c1; *)
            Format.fprintf fmt "@;@[New ages are %a@]@]"
              (A.print_delta c1.ages) c2.ages;
          end
    | _ -> A.print_delta c2.ages fmt c1.ages


  (* let is_var cache addr = A.is_var cache.ages (get_block_addr cache addr) *)

  (* For this domain, we don't care about time *)
  let elapse env d = env
  
end

