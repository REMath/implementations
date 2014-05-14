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
       * Neither the name of the University of Virginia  nor the names 
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

open Hashset

(* NFAs *)

type symbolset = string hashset 
type 's delta = ('s, ('s, symbolset) Hashtbl.t) Hashtbl.t (* state -> state -> symbolset *)
type 's epsilon = ('s, ('s, bool) Hashtbl.t) Hashtbl.t    (* state -> stateset *)


type statespace  = Base      of string
                   | InCross of statespace * statespace
		   | InLHS   of statespace 
 		   | InRHS   of statespace 

type symbol = Character of string 
	      | Epsilon

let nfa_count = ref 0

type nfa = { 
  i       : int;
  s       : statespace;
  f       : statespace;
  delta   : statespace delta;
  epsilon : statespace epsilon;
  q       : (statespace, bool) Hashtbl.t
}

(* add single transition s1 -c-> s2 *)
let add_trans (nfa : nfa)
              (s1 : statespace) 
	      (c  : symbol)
	      (s2 : statespace) =
  let _ = Hashtbl.replace nfa.q s1 true;
          Hashtbl.replace nfa.q s2 true in
  match c with
    | Character c ->
	let deltamap = (try 
			  Hashtbl.find nfa.delta s1 
			with Not_found -> 
			  let newmap = Hashtbl.create 50 in
			    Hashtbl.replace nfa.delta s1 newmap; newmap) in
	let charset = (try 
			 Hashtbl.find deltamap s2 
		       with Not_found -> 
			 let newmap = Hashtbl.create 256 in
			   Hashtbl.replace deltamap s2 (Enum newmap); (Enum newmap))  in
	  set_add charset c
    | Epsilon ->
	let epsilonset = (try
			    Hashtbl.find nfa.epsilon s1
			  with Not_found ->
			    let newset = Hashtbl.create 50 in
			      Hashtbl.replace nfa.epsilon s1 newset ; newset) in
	  Hashtbl.replace epsilonset s2 true

(* add transitions s -c-> for any c *)
let add_all_trans (nfa : nfa)
                  (s1 : statespace) 
	          (s2 : statespace) =
  let _ = Hashtbl.replace nfa.q s1 true;
          Hashtbl.replace nfa.q s2 true in
  let deltamap = (try 
		    Hashtbl.find nfa.delta s1 
		  with Not_found -> 
		    let newmap = Hashtbl.create 50 in
		      Hashtbl.replace nfa.delta s1 newmap; newmap) in
    Hashtbl.replace deltamap s2 AllElements

(* Construct NFA with integer state space *)

let new_nfa () : nfa =
  let i = !nfa_count in
  let _ = incr nfa_count in
  let s = Base "1" in
  let f = Base "2" in
  let delta = Hashtbl.create 50 in
  let epsilon = Hashtbl.create 50 in
  let q = Hashtbl.create 2 in
  let _ = Hashtbl.replace q s true;
          Hashtbl.replace q f true in
    { i = i;
      s = s;
      f = f;
      delta = delta;
      epsilon = epsilon;
      q = q
    }

let new_nfa_states (s: statespace) (f : statespace) : nfa =
  let i = !nfa_count in
  let _ = incr nfa_count in
  let delta = Hashtbl.create 50 in
  let epsilon = Hashtbl.create 50 in
  let q = Hashtbl.create 2 in
  let _ = Hashtbl.replace q s true;
          Hashtbl.replace q f true in
    { i = i;
      s = s;
      f = f;
      delta = delta;
      epsilon = epsilon;
      q = q
    }

let nfa_rename_states nfa s f =
  let q = nfa.q in
  let _ = Hashtbl.remove q nfa.s in
  let _ = Hashtbl.remove q nfa.f in
  let _ = Hashtbl.replace q s true in
  let _ = Hashtbl.replace q f true in
    { nfa with s = s; f = f; q = q } 


(* Construct NFA that accepts \Sigma^* *)

let new_sigmastar () : nfa =
  let newnfa = new_nfa_states (Base "a") (Base "b") in
    add_trans newnfa newnfa.s Epsilon newnfa.f;
    add_all_trans newnfa newnfa.f newnfa.f;
    newnfa


(* Pretty print NFA in a format that is compatible
   with our lexer/parser 
*)

let rec string_of_state x = match x with 
  | Base s -> s
  | InCross(a, b) -> (string_of_state a) ^  (string_of_state b)
  | InLHS a -> (string_of_state a)
  | InRHS b -> (string_of_state b)

let print_nfa nfa =
  Printf.printf "\n      [ s: %s\n        f: %s\n        d:\n"
      (string_of_state nfa.s) (string_of_state nfa.f);
    Hashtbl.iter (fun s1 m ->
	            (Hashtbl.iter
		       (fun s2 cs -> Printf.printf "           %s -> %s on "
			  (string_of_state s1) (string_of_state s2);
			  (match cs with
			    | Enum cs -> 
				(Printf.printf "{";
				 Hashtbl.iter (fun c _ -> Printf.printf "'%s', " c) cs;
				 Printf.printf "}\n")
			    | AllElements   -> Printf.printf "any\n")
		       ) m)
		 ) nfa.delta;
    Hashtbl.iter (fun s1 m ->
		    Hashtbl.iter (fun s2 _ -> Printf.printf "           %s -> %s on { epsilon }\n"
				    (string_of_state s1) (string_of_state s2)
				 ) m
		 ) nfa.epsilon;
    Printf.printf "       ];\n";
    ()

(* NFA intersection *)

let double_ht_iter a b f = 
  Hashtbl.iter (fun p q -> 
		  Hashtbl.iter (fun r s -> 
				  f p q r s)  b
	       ) a

let intersect (a : nfa) 
              (b : nfa) : nfa = 

  let s = InCross(a.s, b.s) in
  let f = InCross(a.f, b.f) in 
  let q = Hashtbl.create ((Hashtbl.length a.q) * (Hashtbl.length b.q)) in
  let _ = double_ht_iter a.q b.q 
    (fun (a : statespace) _ (b : statespace) _ ->
       Hashtbl.replace q (InCross(a,b)) true) in

  (* delta *)
  let delta = Hashtbl.create 500 in
  let _ = double_ht_iter (a.delta) (b.delta)
    (fun (p : statespace) (q : (statespace, symbolset) Hashtbl.t)   (* in a*)
         (r : statespace) (s : (statespace, symbolset) Hashtbl.t) -> (* in b*)
       double_ht_iter q s 
	 (fun (t : statespace) (u : symbolset)     (* in a *)
	      (v : statespace) (w : symbolset) ->  (* in b *)
	    let old_map = try Hashtbl.find delta (InCross(p,r)) with 
		Not_found -> 
		  let newmap = Hashtbl.create 50 in
		  let _ = Hashtbl.replace delta (InCross(p,r)) newmap in
		    newmap in
	    let newset = set_cap u w in
	      if not (set_empty newset) then 
		Hashtbl.replace old_map (InCross(t,v)) newset
	      else ()
	 )
    ) in
  (* epsilon *)
  let epsilon = Hashtbl.create 500 in
  let _ = double_ht_iter (a.epsilon) (b.epsilon)
    (fun (p : statespace) (q : (statespace, bool) Hashtbl.t)    (* in a*)
         (r : statespace) (s : (statespace, bool) Hashtbl.t) -> (* in b*)
	   double_ht_iter q s 
	     (fun (t : statespace) _     (* in a *)
		  (v : statespace) _ ->  (* in b *)
		    let old_map = try Hashtbl.find epsilon (InCross(p,r)) with
			Not_found ->
			  let newmap = Hashtbl.create 50 in
			  let _ = Hashtbl.replace epsilon (InCross(p,r)) newmap in
			    newmap
		    in Hashtbl.replace old_map (InCross(t,v)) true)
    ) in 
  let _ = double_ht_iter (a.epsilon) (b.q)
    (fun (p : statespace) (q : (statespace, bool) Hashtbl.t)
         (r : statespace) _ ->
	   Hashtbl.iter (fun (t : statespace) _ ->
			   let old_map = try Hashtbl.find epsilon (InCross(p,r)) with
			       Not_found ->
				 let newmap = Hashtbl.create 50 in
				 let _ = Hashtbl.replace epsilon (InCross(p,r)) newmap in
				   newmap
			   in Hashtbl.replace old_map (InCross(t,r)) true) q) in

  let _ = double_ht_iter (a.q) (b.epsilon)
    (fun  (p : statespace) _
          (r : statespace) (s : (statespace, bool) Hashtbl.t) ->
	   Hashtbl.iter (fun (t : statespace) _ ->
			   let old_map = try Hashtbl.find epsilon (InCross(p,r)) with
			       Not_found ->
				 let newmap = Hashtbl.create 50 in
				 let _ = Hashtbl.replace epsilon (InCross(p,r)) newmap in
				   newmap
			   in Hashtbl.replace old_map (InCross(p,t)) true
			) s) in
      
  let i = !nfa_count in
  let _ = incr nfa_count in
    { i = i;
      s = s;
      f = f;
      delta = delta;
      epsilon = epsilon;
      q = q;
    }

let copytable s t f = Hashtbl.iter 
  (fun s1 m -> 
     let old_map = try Hashtbl.find t (f s1) with
	 Not_found -> 
	   let newmap = Hashtbl.create 50 in
	   let _ = Hashtbl.replace t (f s1) newmap in
	     newmap 
     in
       Hashtbl.iter
	 (fun s2 cs -> Hashtbl.replace old_map (f s2) cs) m
  ) s 


let concat (a : nfa)
           (b : nfa) : nfa =
  let s = InLHS a.s in
  let f = InRHS b.f in
    
  let q = Hashtbl.create ((Hashtbl.length a.q) + (Hashtbl.length b.q)) in
  let _ = Hashtbl.iter (fun state _ -> Hashtbl.replace q (InLHS state) true) a.q in
  let _ = Hashtbl.iter (fun state _ -> Hashtbl.replace q (InRHS state) true) b.q in

  let delta = Hashtbl.create 500 in
  let _ = copytable a.delta delta (fun x -> InLHS x) in
  let _ = copytable b.delta delta (fun x -> InRHS x) in

  let epsilon = Hashtbl.create 500 in

  let _ = copytable a.epsilon epsilon (fun x -> InLHS x) in
  let _ = copytable b.epsilon epsilon (fun x -> InRHS x) in

  (* epsilon - middle *)
  let old_map = try Hashtbl.find epsilon (InLHS a.f) with
      Not_found ->
	let newmap = Hashtbl.create 1 in
	let _ = Hashtbl.replace epsilon (InLHS a.f) newmap in 
	  newmap in
  let _ = Hashtbl.replace old_map (InRHS b.s) true in

  let i = !nfa_count in
  let _ = incr nfa_count in
    { i = i;
      s = s;
      f = f;
      delta = delta;
      epsilon = epsilon;
      q = q;
    }

let forward_fold_nfa (f : statespace -> 'a -> 'a) (nfa : nfa) (acc : 'a) = 
  let queue   = [ nfa.s ] in
  let v = Hashtbl.create 500 in
  let visited x = try Hashtbl.find v x with Not_found -> false in
  let visit x = Hashtbl.replace v x true in
  let neighbors q = 
    let outbound = try Hashtbl.find nfa.delta q with Not_found -> Hashtbl.create 0 in
    let deltaneighbors = Hashtbl.fold (fun state _ acc -> state::acc) outbound [] in
    let outbound = try Hashtbl.find nfa.epsilon q with Not_found -> Hashtbl.create 0 in
    let epsilonneighbors = Hashtbl.fold (fun state _ acc -> state::acc) outbound [] in
      deltaneighbors @ epsilonneighbors
  in  
  let rec walk queue acc = 
    let q = List.hd queue in
      if (visited q) && (List.length queue > 1) then
	walk (List.tl queue) acc
      else if visited q then
	acc
      else
	let newacc = f q acc in
	let _ = visit q in
	let victims = neighbors q in
	let queueadd = List.fold_left (fun acc x -> 
					 if not (visited x) then
					   x::acc
					 else
					   acc) [] victims in
	   walk (queue@queueadd) newacc
  in
    walk queue acc
  
    
(* Walk NFA to see if it accepts any strings *)

let is_empty nfa = 
  let res = forward_fold_nfa (fun n acc -> acc || (n = nfa.f)) nfa false in
    not res


(* find states in this NFA *)

let states_of nfa =
  Hashtbl.fold (fun x _ acc -> x::acc) nfa.q []



let copy_nfa nfa = 
  let delta = Hashtbl.create (Hashtbl.length nfa.delta) in
  let epsilon = Hashtbl.create (Hashtbl.length nfa.epsilon) in
  let id x = x in
  let _ = copytable nfa.delta delta id in
  let _ = copytable nfa.epsilon epsilon id in 
    { nfa with delta = delta;
        epsilon = epsilon;
	q = (Hashtbl.copy nfa.q) }
	
      
    
