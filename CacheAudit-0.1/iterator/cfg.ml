(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(* This module builds the control flow graph of the program being analyzed. 
   The graph is built in five phases:

    1.All the edges (jumps, calls, rets) are collected along with their context.
      The context is a stack of addresses of the function calls in the code. 

    2.Using the targets of those edges, all prebasicblocks are collected along with
      the post_edges (explained in makecfg and collectbasicblocks functions).

    3.These prebasicblocks are wired together.

    4.All prebasicblocks are converted into basicblocks by creating a basicblock for every
      different context that goes trhough a prebasicblock.

    5.Connections between basicblocks are built by mirroring those in the prebasicblocks.

  The difference between prebasicblocks and basicblocks is the information they store about
  their connection to other pre/basicblocks. In the case of prebasicblocks they can have
  multiple connections to the same prebasicblock with different edge contexts.
*)

module IntSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = int
  end )

type context = int list
type edge_type = InternalEdge | ReturningEdge | CallingEdge of int
type edge = context * edge_type * int * int

module EdgeSet = Set.Make(
  struct
    let compare=Pervasives.compare
    type t=edge
  end)

open X86Types
open AsmUtil

let verbose = ref false

(*Control Flow Graph*)
type prebasicblock =
    {
      p_start_addr : int;                         (* start address of basic block *)  
      p_end_addr : int;
      p_next_block_addr : int;
      p_content : (int * instr) list;       (* address,instruction-pairs *)
      p_jump_command : instr option; (* final instruction, does not appear in content *)
      mutable p_out_edges : (edge * prebasicblock) list;
      mutable p_in_edges: (edge * prebasicblock) list
    }
type basicblock =
    {
      start_addr : int;                         (* start address of basic block *)  
      end_addr : int;
      next_block_addr : int;
      content : (int * instr) list;       (* address,instruction-pairs *)
      jump_command : instr option; (* final instruction, does not appear in content *)
      context : context; (* stack of calls to get to this block *)
      mutable out_edges : basicblock list;
      mutable in_edges: basicblock list
    }      
type t = basicblock list

module ContextBlockMap = Map.Make(
  struct
    let compare=Pervasives.compare
    type t= context * int
  end)

let addr_ending_block   = -1
let addr_error_block    = -2
let addr_starting_block = -3
(* Starting addr has the lowest value because it should be the first one
   in the list of nodes of the cfg. *)


let new_block sa en nb cont = 
  let rec extract_last = function
      [] -> failwith "Empty list argument to extract_last\n"
    | [l] -> [], l
    | x::ll -> let beg,l = extract_last ll in x::beg,l
  in
  let c,j = match cont with
      [] -> [], None
    | _ -> let beg,(_,l) = extract_last cont in
      ( match l with
        Jcc _ | Jmp _ | Ret | Halt | Call _ -> beg, Some l
      | _ -> cont, None
      )
  in { p_start_addr = sa;
       p_end_addr   = en;
       p_next_block_addr =  nb;
       p_content    = c;
       p_jump_command = j;
       p_out_edges  = [];
       p_in_edges   = [];
     }

(*Print block *)
let pp_block_addr fmt n = 
  if n = addr_starting_block then Format.fprintf fmt "@ START"
  else if n = addr_error_block then Format.fprintf fmt "@ ERROR"
  else if n = addr_ending_block then Format.fprintf fmt "@ FINAL"
  else Format.fprintf fmt "@<6>0x%x" n
 
let pp_block_header fmt b =
  Format.fprintf fmt "Start: %a @ End: %a @ Next: %a@."
    pp_block_addr b.start_addr pp_block_addr b.end_addr
    pp_block_addr b.next_block_addr
 
let pp_block fmt b =
  Format.fprintf fmt "@[%a@[" pp_block_header b;
  List.iter (function (a,c) -> Format.fprintf fmt "%a %a@." 
          pp_block_addr a X86Print.pp_instr c) b.content;
  ( match b.jump_command with None -> ()
  | Some ins -> Format.fprintf fmt "%a %a@." pp_block_addr b.end_addr X86Print.pp_instr ins
  );
  Format.printf "Edges to: "; List.iter (function x->Format.fprintf fmt "%a@ " pp_block_addr x.start_addr) b.out_edges;
  Format.printf"@.@]\n@]"

let pp_context fmt ctx =
    Format.fprintf fmt "@[("; List.iter (fun i -> Format.fprintf fmt "0x%x " i) ctx; Format.fprintf fmt ")@]"

(* Returns last element of list, fails if list is empty *)
let rec last = function
  | [x] -> x
  | (x::xs) -> last xs
  | _ -> failwith "Empty lists have no last elements"

(* Returns the same list without the first element, if there is one *)
let strip_first = function
  | [] -> []
  | [x] -> []
  | first::rest -> rest

(* Returns wether the first and second elements are equal *)
let first_equals element = function
  | [first] | first::_ -> (compare first element) = 0
  | _ -> false

(* Apply edge transition to context *)
let ctx_apply_t ctx = function
  | InternalEdge -> ctx
  | ReturningEdge -> strip_first ctx
  | CallingEdge addr -> addr::ctx

(* Takes a section and an X86Types.address types and returns the value stored there *)
(* May raise X86Headers.InvalidVirtualAddress *)
let strip_lookup sect addr =
  match addr.addrBase with
    | Some _ -> failwith "Relative addressing failure"
    | None -> match addr.addrIndex with
	| Some _ -> failwith "Relative addressing failure"
	| None -> match addr.segBase with
	    | Some _ ->  failwith "Relative addressing failure"
	    | None -> 
	      let y = X86Headers.lookup sect addr.addrDisp in
	      let x=X86Headers.virtual_to_offset sect y
	      in x 

(* The function that checks if we should recurse (If the edge hasn't been already added) *)
let rec_call edge edges f =
  if EdgeSet.mem edge edges then edges
  else f (EdgeSet.add edge edges)

(* 
   getaddresses: section,  bits |-> EdgeSet
   Collects edges of the CFG in form (source address, target address)
*)
let getedges sections bs =
  if !verbose then Format.printf "getedges \n";
  let rec getaux context ret b edges = 
    if more b then
      let i,nb = X86Parse.read_instr b in
      let src = get_byte b in
      let nsrc = get_byte nb in
      if !verbose then
        Format.printf "Context %a @<6>%x %a@." pp_context context (get_byte b) X86Print.pp_instr i;
      match i with 
	| Jcc (_,x) -> 
	  let tgt = Int64.to_int x in
	  let edge1 = (context, InternalEdge, src, tgt) in 
	  let edge2 = (context, InternalEdge, src, nsrc) in
	  let nedges = rec_call edge1 edges (getaux context ret (goto b tgt)) in
    rec_call edge2 nedges (getaux context ret nb)
	(* Three cases JmpInd *)
	| Jmp (Imm x) ->
	  let tgt = Int64.to_int x in 
	  let edge = (context, InternalEdge, src,tgt) in
    rec_call edge edges (getaux context ret (goto b tgt))
	| Jmp (Address x) ->
	  (try
      let tgt = strip_lookup sections x in 
		  let edge = (context, InternalEdge, src,tgt) in
      rec_call edge edges (getaux context ret (goto b tgt))
	   with X86Headers.InvalidVirtualAddress -> EdgeSet.add (context,InternalEdge,src,addr_error_block) edges)
	| Jmp (Reg _) -> failwith "Relative addressing failure"
	| Call (Imm x) ->  
	  let tgt = Int64.to_int x in 
	  let edge = (context, CallingEdge(src), src,tgt) in
    let nedges = if first_equals src context then failwith "Recursion not supported" 
                 else rec_call edge edges (getaux (src::context) nsrc (goto b tgt)) in
    (* now we add the edges to the rest of the current context *)
    getaux context ret nb nedges
	| Call (Address x) ->  
	  let nedges = (try
      let tgt = strip_lookup sections x in 
	    let edge = (context, CallingEdge(src), src,tgt) in
      if first_equals src context then failwith "Recursion not supported"
      else rec_call edge edges (getaux (src::context) nsrc (goto b tgt))
	   with X86Headers.InvalidVirtualAddress -> EdgeSet.add (context,InternalEdge,src,addr_error_block) edges) in
    getaux context ret nb nedges
	| Call (Reg _) -> failwith "Relative addressing failure"
	| Ret -> EdgeSet.add (context, ReturningEdge, src, ret) edges  (*return to calling context *)
	| _ -> getaux context ret nb edges
    else edges
  in getaux [] addr_ending_block bs EdgeSet.empty

(* 
   val collectbasicblocks : bits -> ((int * instr) list , int list) list
   first component of return value is basic block,
   second component is list of targets of outgoing edges
   basic block starts <=> address is jump target bs
   basic block ends  <=> (1) Jmp x etc  *or* (2) next address in getaddresses bs 
*)   

let collectbasicblocks edges bs =
  (* Collect all nonnegative jmp targets *)
  let targets = EdgeSet.fold (fun (_,_,_,tgt) set -> if tgt>=0 then IntSet.add tgt set else set) edges IntSet.empty in
  let rec read_block init ad = 
    let c,nb = X86Parse.read_instr (goto bs ad) in
    let nad = get_byte nb in
    match c with                          (* block termination condition 1 *)
      | Jmp _ | Jcc _ | Call _ | Ret | Halt -> (([(ad,c)],nad), None)
      | _ -> 
	     if IntSet.mem nad targets                     (* block termination condition 2 *)
	     then (
        let contexts = EdgeSet.filter (fun (_,_,_,tgt) -> tgt = init) edges in
        let nedges = EdgeSet.fold (fun (ctx,edge_t,_,_) nes -> let nctx = ctx_apply_t ctx edge_t in (nctx,InternalEdge,ad,nad)::nes ) contexts [] in
        ([(ad,c)],nad), Some(nedges))
	     else let (cs,nad),es = read_block init nad in ((((ad,c)::cs),nad),es)
  in 
  IntSet.fold 
    (fun ad (cs,es) -> 
        let (c,e) = read_block ad ad in 
        (c::cs , match e with None -> es | Some e -> List.fold_left (fun es x -> EdgeSet.add x es) es e)
    ) targets ([],EdgeSet.empty)


(** Deepcopies all appearences of functions being called more than once.
    First all preblocks are transformed into one or more basic blocks 
    (depending on the number of different context passing through them)
    with no edge information. And then all the edges are wired using the
    original list of basicblocks. *)
let clone_functions cfg =
  let copy_block_wo_edges b ctx = {
    start_addr = b.p_start_addr;
    end_addr = b.p_end_addr;
    next_block_addr = b.p_next_block_addr;
    content = b.p_content;
    jump_command = b.p_jump_command;
    context = ctx;
    out_edges = [];
    in_edges = []
  } in
  (* A bit inneficient in branches. Inserts and replaces every branching node *)
  let newnodes = List.fold_left (fun l n -> 
    match n.p_out_edges with
    (* Blocks with no outgoing edges should have an empty context *)
    | [] -> ContextBlockMap.add ([],n.p_start_addr) (copy_block_wo_edges n []) l
    | _ ->
      List.fold_left(fun l ((cn,_,_,_),_) -> 
        if !verbose then Format.printf "Added block 0x%x with context %a@." n.p_start_addr pp_context cn;
        (* Using a map avoids duplication of blocks when there is a branch. *)
        ContextBlockMap.add (cn,n.p_start_addr) (copy_block_wo_edges n cn) l
      ) l n.p_out_edges
    )ContextBlockMap.empty cfg in
  List.iter (fun n -> 
    List.iter (fun ((ctx,edge_t,src,dst),_) -> try
      let key = ((ctx_apply_t ctx edge_t),dst) in
      let src_block = ContextBlockMap.find (ctx,n.p_start_addr) newnodes in
      let tgt_block = ContextBlockMap.find key newnodes in
      src_block.out_edges <- tgt_block::src_block.out_edges;
      tgt_block.in_edges <- src_block::tgt_block.in_edges;
      with Not_found -> (Format.printf "cloning Edge %a (0x%x, 0x%x) not found with key (%a,0x%x)@." pp_context ctx src dst pp_context (ctx_apply_t ctx edge_t) dst; raise Not_found)
    ) n.p_out_edges
  ) cfg;
  (* Return only the values of the map *)
  List.map (fun (k,v) -> v ) (ContextBlockMap.bindings newnodes)


(* Builds cfg from section info and start address
   using the method described in the top of the file *)

let makecfg start sections=
  let bs = goto (X86Headers.get_bits sections) start in
  let makeblock (commands, nb) = new_block (fst (List.hd commands)) 
      (fst (last commands)) nb commands in
  (* pre_edges are those that correspond to blocks that end with jmps etc
     post_edges are those that correspond to blocks that end by being jmped to.
     post_edges are determined when computing basic blocks *)
  let pre_edges = EdgeSet.add ([],InternalEdge,addr_starting_block, start) 
                              (getedges sections bs) in 
  if !verbose then Format.printf "got Edges\n";
  let pre_blocks, post_edges = collectbasicblocks pre_edges bs in
  let edges = EdgeSet.union pre_edges post_edges in
  let start_block = new_block addr_starting_block addr_starting_block 0 [] in
  let basicblocks = 
    [start_block; new_block addr_ending_block 0 0 []; 
     new_block addr_error_block 0 0 []] 
      @ (List.map makeblock pre_blocks) in
  EdgeSet.iter 
    (fun ed ->
      let _,_,src,tgt = ed in
      try
  			let src_block =  List.find (fun x -> x.p_end_addr = src) basicblocks in
  			let tgt_block =  List.find (fun x -> x.p_start_addr = tgt) basicblocks in
  			src_block.p_out_edges <- (ed,tgt_block)::src_block.p_out_edges;
  			tgt_block.p_in_edges <- (ed,src_block):: tgt_block.p_in_edges;
      with Not_found -> (Format.printf "Edge (0x%x, 0x%x) not found\n" src tgt; raise Not_found)
    ) edges;
  if !verbose then Format.printf "Got graph\n"; 
  clone_functions basicblocks

(* Prints control flow graph, blocks separated by newline *)
let printblock = pp_block Format.std_formatter

let printcfg g = Format.printf "CFG is \n";List.iter printblock g




