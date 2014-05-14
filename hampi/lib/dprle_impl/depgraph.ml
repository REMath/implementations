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

type nfa = Nfa.nfa

type inedge = InConcat  of node ref * node ref
	      | InIsect of node ref 

and outedge = OutConcatLeft of node ref * node ref     (* (rhs, target) *)
	      | OutConcatRight of node ref * node ref  (* (lhs, target) *)
	      | OutIsect of node ref
and node = { 
  mutable id   : string;
  mutable lang : nfa option;
  inb  : (inedge, bool)  Hashtbl.t;
  outb : (outedge, bool) Hashtbl.t }
and graph = (string, node) Hashtbl.t


let graph : ((string, node) Hashtbl.t) list ref = ref [ Hashtbl.create 50 ]

let cur_graph () = 
  match !graph with 
    | x::xs -> x
    | _ -> failwith "Lack of context"

let new_node graph id lang : node =
  let newnode = { id = id;
		  lang = lang;
		  inb  = Hashtbl.create 10;
		  outb = Hashtbl.create 10 } in
  let _ = Hashtbl.replace graph id newnode in
    newnode

let find_node graph id = try Hashtbl.find graph id with
    Not_found -> 
      new_node graph id None

let add_concat graph lhs rhs target = 
  let lhs = find_node graph lhs in
  let rhs = find_node graph rhs in
  let target = find_node graph target in
  let lhsout = lhs.outb in
  let rhsout = rhs.outb in
  let targetin = target.inb in
    Hashtbl.replace lhsout   (OutConcatLeft(ref rhs, ref target)) true;
    Hashtbl.replace rhsout   (OutConcatRight(ref lhs, ref target)) true;
    Hashtbl.replace targetin (InConcat(ref lhs, ref rhs)) true

let add_isect graph source target =
  let source = find_node graph source in
  let target = find_node graph target in
  let sourceout = source.outb in
  let targetin  = target.inb in
    Hashtbl.replace sourceout (OutIsect (ref target)) true;
    Hashtbl.replace  targetin  (InIsect (ref source)) true

let remove_inb target edge =
  Hashtbl.remove (target.inb) edge;
  match edge with
    | InConcat(a, b) -> 
	let removematching node edge = Hashtbl.remove (node.outb) edge in
	  removematching !a (OutConcatLeft(b, ref target));
	  removematching !b (OutConcatRight(a, ref target))
    | InIsect source -> Hashtbl.remove (!source.outb) (OutIsect (ref target))
	
let remove_outb source edge = 
  Hashtbl.remove (source.outb) edge;
  (match edge with
    | OutConcatLeft (rhs, target) -> 
(* 	Printf.printf "\nE: %s = Concat(%s,%s)\n" !target.id source.id !rhs.id;  *)
	Hashtbl.remove (!rhs.outb) (OutConcatRight(ref source, target));
	Hashtbl.remove (!target.inb) (InConcat(ref source, rhs))
    | OutConcatRight (lhs, target) ->
(* 	Printf.printf "\nE: %s = Concat(%s,%s)\n" !target.id !lhs.id source.id; *)
	Hashtbl.remove (!lhs.outb) (OutConcatLeft(ref source, target));
	Hashtbl.remove (!target.inb) (InConcat(lhs, ref source))
    | OutIsect target ->
(* 	Printf.printf "\nE: %s subset %s\n" !target.id source.id;  *)
	Hashtbl.remove (!target.inb) (InIsect (ref source)))


let rename_node defgraph id newid =
  ()



 let print_graph graph = 
  Hashtbl.iter (fun id node ->
		  let _ = Hashtbl.iter (fun edge _ -> match edge with 
					  | InConcat(x,y) -> Printf.printf "# %s subset Concat(%s,%s)\n" id (!x.id) (!y.id)
					  | InIsect x -> Printf.printf "# %s subset %s\n" id (!x.id)) node.inb in
		  let _ = match node.lang with
		    | Some m ->  
			Printf.printf "\n%s =" id;
			Nfa.print_nfa m;
			if Nfa.is_empty m then
			  Printf.printf "# Language is empty!\n" 
		    | _ -> () in ()
	       ) graph

let copy_graph graph = 
  let copy_node n = { n with outb = Hashtbl.copy n.outb;
			     inb  = Hashtbl.copy n.inb;
		             lang = match n.lang with 
		               | None -> None
		               | Some x -> Some (Nfa.copy_nfa x) } in
  let nodes = Hashtbl.fold (fun _ node acc -> (copy_node node)::acc) graph [] in 
  let newgraph = Hashtbl.create (Hashtbl.length graph) in
  let _ = List.iter (fun x -> Hashtbl.replace newgraph (x.id) x) nodes in
  let _ = Hashtbl.iter (fun _ node -> 
			  let fix x = ref (find_node newgraph !x.id) in 
			  let fix_out outedge = match outedge with
			    | OutConcatLeft(rhs, target)  -> OutConcatLeft(fix rhs, fix target)
			    | OutConcatRight(lhs, target) -> OutConcatRight(fix lhs, fix target)
			    | OutIsect target             -> OutIsect (fix target) in
			  let fix_in inedge = match inedge with
			    | InConcat(lhs, rhs) -> InConcat(fix lhs, fix rhs)
			    | InIsect source     -> InIsect (fix source) in
			  (* fix outbound edges *)
			  let edgelist = Hashtbl.fold (fun outedge _ acc -> outedge::acc) node.outb [] in
			  let newedgelist = List.map fix_out edgelist in
			  let _ = Hashtbl.clear node.outb in
			  let _ = List.iter (fun x -> Hashtbl.replace node.outb x true) newedgelist in
                          (* fix inbound edges *)
			  let edgelist = Hashtbl.fold (fun outedge _ acc -> outedge::acc) node.inb [] in
			  let newedgelist = List.map fix_in edgelist in
			  let _ = Hashtbl.clear node.inb in
			    List.iter (fun x -> Hashtbl.replace node.inb x true) newedgelist
		       ) newgraph
  in 
    newgraph

let push () = 
  match !graph with
    | x::xs -> graph := (copy_graph x)::!graph
    | _-> failwith "Lack of context."

exception Pop

let pop () =
  match !graph with
    | [x] -> raise Pop
    | x::xs -> graph := xs
    | _ -> failwith "Shouldn't happen."

