(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)

open Big_int
open AD.DS


module IntSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = int
  end )

type cache_st = H | M | N | HM
(* Hit, Miss, No access, Hit or Miss *)
    
let duration_H, duration_M, duration_N = 3,20,1

let max_times = 10000000




module Make (CA : CacheAD.S) = struct
  
  type 'a parent_t = Root | Single of 'a | Couple of 'a * 'a
  
  module rec Trie : sig 
    type t = {
      parents : t parent_t;
      parent_UIDs : IntSet.t;
      node_UID : int;
      value: cache_st option;
      num_traces: big_int;
    }  
    val compare : t -> t -> int
  end
   = struct
    type t = {
      parents : t parent_t;
      parent_UIDs : IntSet.t;
      node_UID : int;
      value: cache_st option;
      num_traces: big_int;
    }
    let compare n1 n2 = 
      Pervasives.compare (n1.value, n1.parent_UIDs) (n2.value,n2.parent_UIDs)
  end   
  
  and TrieSet : Set.S  with type elt = Trie.t
    = Set.Make(Trie)

  type t = {
    traces : Trie.t add_top;
    cache : CA.t;
    times: IntSet.t add_top;
  }
  
  
  (* Calculates a hash given the current value of a node *)
  (* and the unique IDs of the parents*)
  let hash_node_parents value parent_UIDs = 
    Hashtbl.hash (value, parent_UIDs)
    
  module HT = struct
    type t = Trie.t
    let hash node = hash_node_parents node.Trie.value node.Trie.parent_UIDs
    let equal n1 n2 = (Trie.compare n1 n2 = 0)
  end
  
  module HashTable = Hashtbl.Make(HT)
  
  let is_dummy n = (n.Trie.value = None)
  
  let get_parent_UIDs = function
    | Root -> IntSet.empty
    | Single p -> IntSet.singleton p.Trie.node_UID
    | Couple (p1,p2) -> 
      (* In case that a parent p1 is dummy and p2 not, *)
      (* parent_uids = {p2} union (parent_UIDs of p1) *)
      if (is_dummy p1) || (is_dummy p2) then begin
        (* assertion: cannot have two dummy parents *)
        assert (is_dummy p1 <> is_dummy p2);
        let p1,p2 = if is_dummy p2 then (p2,p1) else (p1,p2) in
        IntSet.add p2.Trie.node_UID p1.Trie.parent_UIDs
      end else
        let puids = IntSet.add p1.Trie.node_UID IntSet.empty in
        IntSet.add p2.Trie.node_UID puids
        
  
  (* get the number of traces finishing on the parents *)
  let get_parent_num_traces parents = match parents with
    | Root -> unit_big_int
    | Single p -> p.Trie.num_traces
    | Couple (p1,p2) -> add_big_int p1.Trie.num_traces p2.Trie.num_traces
  
  let uid = ref 0
  
  let create_node parents value =  
    incr uid;
    let num_tr = 
        mult_int_big_int (if value = Some HM then 2 else 1) 
        (get_parent_num_traces parents) in
    let parent_UIDs = get_parent_UIDs parents in
    {
      Trie.parents = parents;
      Trie.parent_UIDs = parent_UIDs;
      Trie.value = value;
      Trie.node_UID = !uid;
      Trie.num_traces = num_tr;
    }
    
  (* A hash table holding all nodes exactly once *)
  let hash_table = HashTable.create 500
  
  (* Find the value in the hash table or add it; return the node *)
  let find_or_add node = try
    HashTable.find hash_table node
    with Not_found -> 
      HashTable.add hash_table node node;
      node
    
  let root =  
    let node = create_node Root (Some N) in
    HashTable.add hash_table node node;
    node
    
  let init cache_param =
    { traces = Nt root; cache = CA.init cache_param; times = Nt (IntSet.singleton 0)} 
        
  let get_single_parent = function
    | Single p -> p
    | _ -> failwith "TraceAD: only single parent is expected"
  
  (* Update node's value*)
  let update_value node value = 
    if value = node.Trie.value then node
    else begin
      let new_node = create_node node.Trie.parents value in
      let new_node = find_or_add new_node in
      new_node
    end

  

  (* Add a new child to a node *)
  let add trace value = 
    match trace with
    | Tp -> Tp
    | Nt node ->
      let new_node = create_node (Single node) (Some value) in
      let new_node = find_or_add new_node in
      Nt new_node
  
  let add_dummy parents =
    let new_node = create_node parents None in
    find_or_add new_node
  
  let join_traces trace1 trace2 =
    match trace1,trace2 with
    | (Tp,_) | (_,Tp) -> Tp
    | Nt node1, Nt node2 -> 
      (* Same trie *)
      if node1.Trie.node_UID = node2.Trie.node_UID then Nt node1
      (* Same parents *)
      else if node1.Trie.parent_UIDs = node2.Trie.parent_UIDs then begin
        (* assertion: if parents and values were equal, should have same UID *)
        assert (node1.Trie.value <> node2.Trie.value);
        if node1.Trie.value <> (Some N) && node2.Trie.value <> (Some N) then begin
          Nt (update_value node1 (Some HM)) 
        end else failwith "TraceAD: Joining 'N' not implemented" end
      else
        let parents = Couple (node1,node2) in 
        (* A dummy node whose parents are the nodes we are joining *)
        Nt (add_dummy parents)

  let join_times times1 times2 = 
    match times1,times2 with
    | Nt tms1,Nt tms2 ->
      let tms = IntSet.union tms1 tms2 in
      if IntSet.cardinal tms < max_times then Nt tms else Tp
    | _,_ -> Tp
  
  let join env1 env2 =
    let traces = join_traces env1.traces env2.traces in
    let cache = CA.join env1.cache env2.cache in
    let times = join_times env1.times env2.times in
    {traces = traces; cache = cache; times = times}
        
  let widen env1 env2 = 
    let cache = CA.widen env1.cache env2.cache in
    (* join_times goes to top at some point *)
    let times = join_times env1.times env2.times in
    let traces = match env1.traces, env2.traces with
      | Nt node1, Nt node2 -> 
        if node1.Trie.node_UID = node2.Trie.node_UID then Nt node1
        else Tp 
    | _,_ -> Tp in
    {cache = cache; traces = traces; times = times}
  
  let rec subseteq_traces trace1 trace2 =
    match trace1,trace2 with
    | _,Tp -> true
    | Tp,_ -> false
    | Nt node1, Nt node2 ->
      if node1.Trie.node_UID = node2.Trie.node_UID then true
      else if (node1.Trie.value = node2.Trie.value) || 
        (node2.Trie.value = Some HM && node2.Trie.value <> None) then
        match node1.Trie.parents,node2.Trie.parents with
        | Root,Root -> true
        | Single p1,Single p2 -> subseteq_traces (Nt p1) (Nt p2)
        | Couple (p11,p12),Couple (p21,p22) ->
          subseteq_traces (Nt p11) (Nt p12) && subseteq_traces (Nt p21) (Nt p22)
        | _,_ -> false
      else false
  
  let subseteq env1 env2 = 
    let subeq_times = match env1.times,env2.times with
    | Nt tms1,Nt tms2 -> IntSet.subset tms1 tms2
    | _,Tp -> true
    | _,_ -> false in 
    (CA.subseteq env1.cache env2.cache) &&
    subeq_times &&
    subseteq_traces env1.traces env2.traces
  
  
  let print fmt env =
    CA.print fmt env.cache;
    Format.fprintf fmt "\n# traces: ";
    match env.traces with
    | Tp -> Format.fprintf fmt "too imprecise to tell"
    | Nt node ->
      Format.fprintf fmt "%s, %f bits\n" 
        (string_of_big_int node.Trie.num_traces) 
        (Utils.log2 node.Trie.num_traces);
    Format.fprintf fmt "\n# times: ";
    match env.times with 
    | Tp -> Format.fprintf fmt "too imprecise to tell"
    | Nt tms ->
      let numtimes = float_of_int (IntSet.cardinal tms) in
      Format.fprintf fmt "%f, %f bits\n" 
        numtimes ((log10 numtimes)/.(log10 2.))
      

    (* N.B. This way of counting traces*)
    (* does not consider possible Error-states; *)
    
  let print_delta  env1 fmt env2 = 
    (* TODO: implement printing of delta of traces and times *)
    CA.print_delta env1.cache fmt env2.cache
  
  let add_time time times = 
    match times with 
    | Tp -> Tp
    | Nt tms -> Nt (IntSet.fold (fun x tms ->
        IntSet.add (x + time) tms) tms IntSet.empty)
  
  let add_time_status status times = 
    match status with
    | H -> add_time duration_H times
    | M -> add_time duration_M times
    | N -> add_time duration_N times
    | HM -> 
      join_times (add_time duration_M times) (add_time duration_H times)
  
  let touch env addr =
    let c_hit,c_miss = CA.touch_hm env.cache addr in
    (* determine if status it is H or M or HM *)
    let cache,status = match c_hit,c_miss with
    | Bot,Bot -> raise Bottom
    | Nb c,Bot -> (c,H)
    | Bot,Nb c -> (c,M)
    | Nb c1,Nb c2   -> (CA.join c1 c2,HM) in
    let traces = add env.traces status in
    let times = add_time_status status env.times in
    {traces = traces; cache = cache; times = times}

  (* Hitmiss tracking for touch_hm *)
  let touch_hm env addr =
    let c_hit,c_miss = CA.touch_hm env.cache addr in
    let nu_hit = match c_hit with
      | Nb c -> 
	Nb {traces = add env.traces H;
  	    cache = c ;
  	    times = add_time_status H env.times}
      | Bot -> Bot
    in
    let nu_miss = match c_miss with
      | Nb c -> 
	Nb {traces = add env.traces M; 
	    cache = c ;
  	    times = add_time_status M env.times}
      | Bot -> Bot
    in (nu_hit,nu_miss)


  let elapse env time = 
    let times = add_time time env.times in
    (* elapse is called after each instruction and adds an "N"-node; *)
    (* in the traces two consecutive N's will correspond to "no cache access"*)
    let traces = add env.traces N in
    let times = add_time_status N times in
    {env with times = times; traces = traces}

  let count_cache_states env = CA.count_cache_states env.cache 

end

