(*  Copyright (c) 2008, University of Virginia
    All rights reserved.
   
    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:
       * Redistributions of source code must retain the above copyright
         notice, this list of conditions and the following disclaimer.
       * Redistributions in binary form must reproduce the above
         copyright notice, this list of conditions and the following
         disclaimer in the documentation and/or other materials
         provided with the distribution.
       * Neither the name of the University of Virginia nor the names 
         of its contributors may be used to endorse or promote products
         derived from this software without specific prior written
         permission.
   
    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
    (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
    SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
    HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
    STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
    ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
    OF THE POSSIBILITY OF SUCH DAMAGE.
   
    Author: Pieter Hooimeijer
*)

open Depgraph
open Nfa

let free (n : node) = 
  Hashtbl.length (n.inb) == 0

let not_done (n : node) =
   Hashtbl.length n.outb > 0

let almostfree (n : node) = 
  Hashtbl.fold (fun edge _ acc -> match edge with
		  | InIsect e -> acc && true
		  | InConcat(_,_) -> (Hashtbl.length n.inb = 1)
	       ) n.inb true

module StringSet = Set.Make (struct 
			       type t = string
			       let compare s1 s2 = compare s1 s2
			     end)

let free_not_done_nodes graph = 
  Hashtbl.fold (fun _ node set -> 
		  if (free node && not_done node) then
		    ref (StringSet.add node.id !set)
		  else 
		    set) graph (ref StringSet.empty)

let unpack (n : nfa option) = match n with
  | None -> Nfa.new_sigmastar ()
  | Some m -> m

let solve_single_forward graph node = 
  let outbound = node.outb in
  let edgefilter edge = match edge with
    | OutConcatLeft(rhs, target)  -> free !rhs && almostfree !target
    | OutConcatRight(lhs, target) -> free !lhs && almostfree !target
    | OutIsect target             -> almostfree !target
  in
  let processedge edge = 
    let cur = unpack node.lang in
    let _ = Depgraph.remove_outb node edge in
    let _ = (match edge with
	       | OutConcatLeft(rhs, target) ->
(*		   Printf.printf "Z: Forward: %s = %s o %s\n" !target.id node.id !rhs.id; *)
		   let rhs = unpack !rhs.lang in
		     (match !target.lang with 
			| None ->  !target.lang <- Some (Nfa.concat cur rhs)
			| Some m -> !target.lang <- Some(Nfa.intersect m (Nfa.concat cur rhs))
		     )
	       | OutConcatRight(lhs, target) ->
(*		   Printf.printf "Z: Forward: %s = %s o %s\n" !target.id !lhs.id node.id ; *)
		   let lhs = unpack !lhs.lang in
		     (match !target.lang with 
			| None   -> !target.lang <- Some (Nfa.concat lhs cur)
			| Some m -> !target.lang <- Some (Nfa.intersect m (Nfa.concat lhs cur))
		     )
	       | OutIsect target ->
(*		   Printf.printf "Z: Forward: %s subset %s\n" !target.id node.id ; *)
		   (match !target.lang with 
		      | None   -> !target.lang <- Some (Nfa.copy_nfa cur)
		      | Some m -> !target.lang <- Some (Nfa.intersect cur m)
		   );
	    ) in ()
  in
    let edgestoprocess = Hashtbl.fold (fun edge _ list -> 
					 if edgefilter edge then edge::list else list
				      ) outbound [] in
      List.iter processedge edgestoprocess

(* forward only, at present *)
let rec solve_forward graph = 
  let curset = free_not_done_nodes graph in
    StringSet.iter (fun x -> solve_single_forward graph (Depgraph.find_node graph x)) !curset


exception Done_finding

let find_free_cycle graph =
  let not_visited = Hashtbl.create (Hashtbl.length graph) in
  let _ = Hashtbl.iter (fun _ node -> Hashtbl.replace not_visited node false) graph in

  let is_in_isect x = match x with
    | InIsect _ -> true
    | _ -> false in
  let is_in_concat x = match x with
    | InConcat (_,_) -> true
    | _ -> false in

  let exists x f   = Hashtbl.fold (fun elt _ acc -> (f elt) || acc) x false in
  let filter x f   = Hashtbl.fold (fun elt _ acc -> if (f elt) then elt::acc else acc) x [] in
  let visited x    = try Hashtbl.find not_visited x with Not_found -> true in
  let visit x      = Hashtbl.remove not_visited x in

  let cur_cycle   = Hashtbl.create (Hashtbl.length graph) in
  let cur_inbound = Hashtbl.create (Hashtbl.length graph) in

  let rec walk queue = 
    let queueadd = ref [] in
    let cur, backw = List.hd queue in
      if (visited cur) && (List.length queue > 1) then
	walk (List.tl queue)
      else if (visited cur) && (Hashtbl.length cur_cycle > 1) then
	true (* found a free cycle *)
      else if visited cur then
	false
      else
	(visit cur;
	 Hashtbl.replace cur_cycle cur true;
	 let inbound =  filter cur.inb is_in_isect in
	 let any_nonfree = List.fold_left (fun acc x-> match x with
					     | InIsect source -> not (free !source) || acc
					     | _ -> false)  false inbound in
	   (if any_nonfree then
	      (Hashtbl.clear cur_cycle;
	       Hashtbl.clear cur_inbound;
	       false) (* didn't find a free cycle *)
	    else
	      (if backw || (exists cur.inb is_in_isect) then
		 let concatin = filter cur.inb is_in_concat in
		   match concatin with
		     | InConcat(lhs,rhs) :: _ -> queueadd := (!lhs,true)::(!rhs, true)::!queueadd
		     | _ -> ()
	       else ();
	       Hashtbl.iter (fun edge _ -> match edge with
			       | OutConcatLeft  (rhs, target) -> queueadd := (!target, false)::!queueadd
			       | OutConcatRight (lhs, target) -> queueadd := (!target, false)::!queueadd
			       | OutIsect target -> ()
			    ) cur.outb;
	       Hashtbl.iter (fun edge _ -> match edge with
			       | InConcat (lhs, rhs) -> () (* do nothing *)
			       | InIsect source -> Hashtbl.replace cur_inbound !source true) cur.inb;
	       let toadd = List.filter (fun (x,_) -> not (visited x)) !queueadd in
	       let newqueue = (List.tl queue) @ toadd in

	       if (List.length newqueue > 0) then
		   walk (newqueue)
	       else 
		 true)))
  in
      try
	(Hashtbl.iter (fun _ node -> 
			if not (visited node) && 
			  (exists node.inb is_in_isect) &&
			  (exists node.inb is_in_concat) &&
			  (walk [ (node, false) ]) then
			    raise Done_finding
			else 
			  ()) graph; None)
      with Done_finding ->
	let newcycle = Hashtbl.create (Hashtbl.length cur_cycle) in
	let _ = Hashtbl.iter (fun node _ -> Hashtbl.replace newcycle node.id true) cur_cycle in
	let newinbound = Hashtbl.create (Hashtbl.length cur_inbound) in
	let _ = Hashtbl.iter (fun node _ -> Hashtbl.replace newinbound node.id true) cur_inbound in
	  Some (newcycle, newinbound)

type dependence  = L of ( (statespace * statespace) list ref ref )
	         | R of ( (statespace * statespace) list ref ref )


let enumerate (set : ('a list, bool) Hashtbl.t) : (('a list, 'a) Hashtbl.t) list = 
  let rec listprod lhs rhs = match lhs with
    | x::xs -> 
	(List.map (fun y -> let cur = Hashtbl.copy x in
		     Hashtbl.replace cur rhs y; cur) rhs)
	@ (listprod xs rhs)
    | _ -> []
  in

  let prod lhs rhs = 
    if List.length lhs = 0 then
      List.map (fun y -> let cur = Hashtbl.create (List.length rhs) in
				Hashtbl.replace cur rhs y; cur) rhs
    else
      listprod lhs rhs
  in
    Hashtbl.fold (fun curlist _ acc -> prod acc curlist) set []


let create_graph assignments up down curgraph =
  let new_graph = Depgraph.copy_graph curgraph in
  (* create bottom machines *) 
  let remove_epsilon nfa lstate rstate =
    match (try Some (Hashtbl.find nfa.epsilon lstate) with Not_found -> None) 
    with
      | Some set -> Hashtbl.remove set rstate
      | _ -> () in

  let find_actual id = Hashtbl.find new_graph id in

  let prep_bottom_machine node =
    let node = find_actual node in
    let lang = match node.lang with 
      | Some x -> x
      | None -> failwith "Shouldn't happen" in
    let visited = Hashtbl.create 10 in

    let constraintlist = Hashtbl.find up node.id in
    let constraintlist = !constraintlist in

    let edgeit (l,r) = remove_epsilon lang l r in
    let process_constraint (_, constraints) =
      match constraints with | L list | R list ->
	let edges = !(!list) in
	  if not (Hashtbl.mem visited edges) then
	    (let (l,r) = Hashtbl.find assignments edges in
	     let _ = List.iter edgeit edges in
	     let _ = Nfa.add_trans lang l Epsilon r in
	       Hashtbl.replace visited edges true) in
      List.iter process_constraint constraintlist
  in
  

  let _ = Hashtbl.iter (fun node _ -> prep_bottom_machine node) up in

    

  let prep_inner_node node _ = 

    let node = find_actual node in
    let constraintlist = Hashtbl.find down node.id in
    let constraintlist = !constraintlist in

    let lang : (nfa option ref)= ref None in

    let process_constraint (bottomnode, constraints) =
      let actualbottom = find_actual bottomnode.id in
      let bottomlang = match actualbottom.lang with
	| Some x -> x
	| None -> failwith "Shouldn't happen" in
	match constraints with
	  | L elts -> 
	      let (desired_final,_) = Hashtbl.find assignments !(!elts) in
		lang := Some (match !lang with 
		  | None -> {bottomlang with f = desired_final } 
		  | Some lang -> Nfa.intersect lang ({bottomlang with f = desired_final}) )
	  | R elts ->
	      let (_ ,desired_start) = Hashtbl.find assignments !(!elts) in
		lang := Some (match !lang with 
		  | None -> {bottomlang with s = desired_start}
		  | Some lang -> Nfa.intersect lang ({bottomlang with s = desired_start}))
    in 
      List.iter process_constraint constraintlist; 
      node.lang <- !lang 
  in
  let _ = Hashtbl.iter prep_inner_node down in
    new_graph

let enumerate_solutions up down graph =
  (* find all unique constraint lists *)
  let constraintset = Hashtbl.create (Hashtbl.length up) in
  let it (_, x) = match x with L x | R x -> Hashtbl.replace constraintset !(!x) true in
  let populate _ elt = List.iter it !elt in
  let _ = Hashtbl.iter populate up in
  let combinations = enumerate constraintset in 
  let process_combination x = create_graph x up down graph in
    List.map process_combination combinations

let filter_solutions cycle graphlist = 
  let empty graph = 
    let actual_node node = Hashtbl.find graph node in
      Hashtbl.fold (fun x _ acc -> 
		      let node = actual_node x in
			match node.lang with
			  | Some x -> not (Nfa.is_empty x) && acc
			  | None -> false
		   ) cycle true in
    List.filter empty graphlist

let fix_graph ( cycle : (string, bool) Hashtbl.t) inbound graph =
  let actual x = Hashtbl.find graph x in
  let in_cycle x = try Hashtbl.find cycle x with Not_found -> false in
  let remove_inb x = match x with 
    | OutIsect x -> in_cycle !x.id
    | _ -> false in
  let remove_cycle x = match x with 
    | OutIsect a -> false
    | OutConcatLeft (rhs, target) -> in_cycle !target.id
    | OutConcatRight (lhs, target) -> in_cycle !target.id in
    
  let cycleit x = 
    Hashtbl.iter (fun edge _ -> if remove_cycle edge then
				  Depgraph.remove_outb x edge) x.outb in
    
  let inbit x = Hashtbl.iter (fun edge _ -> if remove_inb edge then 
				Depgraph.remove_outb x edge) x.outb in

    Hashtbl.iter (fun x _ -> cycleit (actual x)) cycle;
    Hashtbl.iter (fun x _ -> inbit (actual x)) inbound
      
let solve_cycle graph cycle inbound =
  let cycle_copy = Hashtbl.copy cycle in 
  let visited = Hashtbl.create (Hashtbl.length cycle) in 
  let in_cycle n = try Hashtbl.find cycle n.id with Not_found -> false in 
  let is_top_node id = 
    let node = Hashtbl.find graph id in
      Hashtbl.fold (fun edge _ acc -> match edge with 
 		      | InConcat(a,b) -> acc && not (in_cycle !a) && not (in_cycle !b)
 		      | InIsect (source) -> acc && not (in_cycle !source) 
		   ) node.inb true in
  let visit n = 
    Hashtbl.replace visited n.id true;
    Hashtbl.remove cycle n.id in

  let visited n = Hashtbl.mem visited n in

  let tracking_up = Hashtbl.create (Hashtbl.length cycle) in 
  let tracking_down = Hashtbl.create (Hashtbl.length cycle) in

  let is_in_isect x = match x with
    | InIsect _ -> true
    | _ -> false in
  let is_free_out_concat x = match x with
    | OutConcatLeft (rhs,_) -> is_top_node !rhs.id
    | OutConcatRight (lhs,_) -> is_top_node !lhs.id
    | _ -> false in

  let filter x f   = Hashtbl.fold (fun elt _ acc -> if (f elt) then elt::acc else acc) x [] in

  let eliminate_top id = 
(*    Printf.printf "Z: Cycle Node: %s\n" id; *)
    let node = Hashtbl.find graph id in 
    let perform_intersect source =
(*      Printf.printf "Z: Cycle: %s subset %s\n" id source.id; *)
      let lhs = unpack node.lang in
      let rhs = unpack source.lang in
      let newlang = Nfa.intersect lhs rhs in
      let _ = node.lang <- Some newlang in
      let states = Nfa.states_of newlang in

      let constraintlist = 
	try Hashtbl.find tracking_up node.id with
	    Not_found -> ref [] in 

      let convert (somenode, constraints) =
	let lhs (l,r) = 
	  List.filter (fun x -> match x with
			 | InCross(a, b) -> a = l
			 | _ -> false) states in
	let rhs (l,r) = 
	  List.filter (fun y -> match y with
			 | InCross(a,b) -> a = r
			 | _ -> false) states in

	let allpairs statepair = 
	  let inner l inacc r =
	    let valid = (try 
			   let x = Hashtbl.find newlang.epsilon l in
			     Hashtbl.find x r
			 with Not_found -> false) in
	      if valid then (l, r)::inacc else inacc
	  in
	  let curlhs = lhs statepair in
	  let currhs = rhs statepair in
	  let outer outacc l = List.rev_append outacc (List.fold_left (inner l) [] (currhs       )) in
	    List.fold_left outer [] (curlhs      )  in

	  match constraints with
	    | L list | R list ->
		if List.length !(!list) > 0 && 
		  try Hashtbl.find newlang.q (fst (List.hd !(!list))) with Not_found -> false then ()
		else 
		  (		     
		    let newlist = List.fold_left (fun acc elt -> List.rev_append acc (allpairs elt)) [] !(!list) in
		    let someset = Hashtbl.create (List.length newlist) in            (* unique elts only *)
		    let _ = List.iter (fun x -> Hashtbl.replace someset x true) newlist in
		    let newlist2 = Hashtbl.fold (fun pair _ acc -> pair::acc) someset [] in
		      (!list) := newlist2)
      in
	List.iter convert !constraintlist
    in

    let perform_concat lhs rhs target = 
(*      Printf.printf "Z: Cycle: %s = %s o %s\n" target.id lhs.id rhs.id; *)
      let convertleft (somenode, constraints) = 
	let downtrack = try Hashtbl.find tracking_down somenode.id with Not_found -> ref [] in
	  Hashtbl.replace tracking_down somenode.id (ref (List.map (fun (downnode, c) -> 
								      if somenode = lhs then (target, c) else (downnode, c)) !downtrack));
	  match constraints with
	    | L list | R list -> 
		let newlist = List.map (fun (x,y) -> (InLHS x, InLHS y)) !(!list) in
		  !list := newlist in


      let convertright (somenode, constraints) = 
	let downtrack = try Hashtbl.find tracking_down somenode.id with Not_found -> ref [] in
	  Hashtbl.replace tracking_down somenode.id (ref (List.map (fun (downnode, c) -> 
								      if somenode = rhs then (target, c) else (downnode, c)) !downtrack));
	  match constraints with
	    | L list | R list -> 
		let newlist = List.map (fun (x,y) -> (InRHS x, InRHS y)) !(!list) in
		  !list := newlist in

      let llang = unpack lhs.lang in
      let rlang = unpack rhs.lang in 
      let newlang = Nfa.concat llang rlang in
      let _ = target.lang <- Some newlang in
(*      let _ = print_nfa llang in
      let _ = print_nfa rlang in 
      let _ = print_nfa newlang in *)

      let leftconstraintlist = try Hashtbl.find tracking_up lhs.id with Not_found -> ref [] in
      let _ = List.iter convertleft !leftconstraintlist in
      let _ = Hashtbl.remove tracking_up lhs.id in

      let rightconstraintlist =  try Hashtbl.find tracking_up rhs.id with Not_found -> ref [] in
      let _ = List.iter convertright !rightconstraintlist in
      let _ = Hashtbl.remove tracking_up rhs.id;
	Hashtbl.replace tracking_up target.id (ref (List.rev_append !leftconstraintlist !rightconstraintlist)) in ()
    in
      
    let inlist = filter node.inb is_in_isect in
    let _ = List.iter (fun x -> match x with
			 | InIsect source -> perform_intersect !source
			 | _ -> ()) inlist in
    let clist = filter node.outb is_free_out_concat in
    let _ = match clist with 
      | [OutConcatRight(lhs, target)] -> 
	  if not (visited !lhs.id) then  ()
(*	    Printf.printf "Z: Other concat node (%s) has not been visited yet.\n" !lhs.id *)
	  else
	    ((*Printf.printf "Z: Other concat node (%s) is ready!\n" !lhs.id; *)
	      perform_concat !lhs node !target;
	     visit !lhs;
	     let lhslang = unpack !lhs.lang in
	     let curlang = unpack node.lang in
	     let curlist = try Hashtbl.find tracking_down !lhs.id with Not_found -> ref [] in
	     let newlist = (ref ([ (InLHS lhslang.f, InRHS curlang.s) ] )) in
	     let _ = Hashtbl.replace tracking_down !lhs.id (ref ((!target, L (ref newlist))::!curlist)) in
	     let curlist = try Hashtbl.find tracking_down node.id with Not_found -> ref [] in
	     let _ = Hashtbl.replace tracking_down node.id (ref ((!target, R (ref newlist))::!curlist)) in

	     let curlist = try Hashtbl.find tracking_up !target.id with Not_found -> ref [] in
	       Hashtbl.replace tracking_up !target.id (ref ((!lhs, L (ref newlist))::(node, R (ref newlist))::!curlist))
	    )
      | [OutConcatLeft(rhs, target)]  -> 
	  if not (visited !rhs.id) then  ()
(*	    Printf.printf "Z: Other concat node (%s) has not been visited yet.2\n" !rhs.id *)
	  else
(*	    (Printf.printf "Z: Other concat node (%s) is ready!\n" !rhs.id; *)
	(      perform_concat node !rhs !target ;
	     visit !rhs;
	     let rhslang = unpack !rhs.lang in
	     let curlang = unpack node.lang in
	     let curlist = try Hashtbl.find tracking_down !rhs.id with Not_found -> ref [] in
	     let newlist = (ref ([ (InLHS curlang.f, InRHS rhslang.s) ] )) in
	     let _ = Hashtbl.replace tracking_down !rhs.id (ref ((!target, R (ref newlist))::!curlist)) in
	     let curlist = try Hashtbl.find tracking_down node.id with Not_found -> ref [] in
	     let _ = Hashtbl.replace tracking_down node.id (ref ((!target, L (ref newlist))::!curlist)) in

	     let curlist = try Hashtbl.find tracking_up !target.id with Not_found -> ref [] in
	       Hashtbl.replace tracking_up !target.id (ref ((!rhs, R (ref newlist))::(node, L (ref newlist))::!curlist))
)

      | [ _ ] -> failwith "Unexpected operation"
      | x::xs -> failwith "Multiple concat ops"
      | _ -> () in
      visit node
  in 
  let rec walk () = 
    let topnodes = filter cycle is_top_node in
      List.iter (fun x -> 
		   if not (visited x) then
		     eliminate_top x
		   else ()) topnodes;
      if Hashtbl.length cycle = 0 then
	()
      else 
	walk ()
  in
  let _ = walk () in
  let _ = fix_graph cycle_copy inbound graph in
  let solutions = enumerate_solutions tracking_up tracking_down graph in
  let solutions = filter_solutions cycle_copy solutions in
    solutions



let solve graph = 
  let queue = ref [graph] in

  let step graph = 
    let _ = Printf.printf "." in
    let _ = solve_forward graph in
      match (find_free_cycle graph) with
	| None -> [ graph ]
	| Some (cycle, inbounds) ->
	    let _ = Printf.printf ":" in
	    solve_cycle graph cycle inbounds
  in

  let donecount graph = Hashtbl.fold (fun _ x acc -> 
				  let y = if not_done x then 0 else 1 in
				    acc + y
			       ) graph 0 in 
  let is_done graph = 
    donecount graph = (Hashtbl.length graph) in

  let rec walk () =
    let q = List.hd !queue in
    let result = step q in
      match result with
	| [] -> Printf.printf "\n# Result: Inconsistent.\n"
	| x::xs -> if is_done x then
	    (Printf.printf "\n# Result: Consistent.\n# Satisfying assignment follows:\n";
	     print_graph x)
	  else
	    let newqueue = match !queue with
	      | x::xs -> xs@result 
	      | _ -> result in
	      queue := newqueue;
	      if (List.length !queue) > 0 then
		walk ()
	      else
		(Printf.printf "\n# Result: Inconsistent.\n"
		)
  in
    walk ()
      
	 

       
