(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)


(* An iterator for analysis of executables *)

(*number of times loops are unrolled before fp computation begins *)
let unroll_count = ref 300
(* if set to false, then we don't unroll the outer loops *)
let unroll_outer_loop = ref true

(* Constants used for timing related analyses.
   Counted in number of cycles *)
let time_skip = 1 (* time taken by a skip *)
let time_jmp = 1  (* time taken by a JMP instruction, in addition to the time taken to read the address. *)
(* time for a JCC is time_jmp + time for the test *)

(* Number of instructions interpreted. For quiet logging *)
let instructions_interpreted = ref 0
let trace = ref false

open Cfg
open AbstractInstr
open AD.DS
open Logger

(* type for weak topological ordering, which can either be
   - Linear: inv can be treated and passed to the nex element
   - SubWto: starts an iteration and when stable goes to the next element
   - wto described in "Efficient Chaotic Iteration Strategies with Widenings" by F. Bourdoncle
*)
type 'a wto = Linear of basicblock*('a wto)
            | SubWto of 'a iteration
            | EmptyWto 

and 'a iteration = {
  head_invariant : 'a add_bottom;
  head_block : basicblock;
  inner_wto  : 'a wto;
  next_wto   : 'a wto;
  unroll_count : int; 
}

let rec pp_wto fmt = function
  EmptyWto -> ()
| Linear(b,w) -> Format.fprintf fmt ", %a%a" pp_block_addr b.start_addr pp_wto w
| SubWto s -> Format.fprintf fmt "@[, (%a%a)@]%a" pp_block_addr s.head_block.start_addr pp_wto s.inner_wto pp_wto s.next_wto

module BlockMap = Map.Make(struct 
  type t = basicblock 
  let compare b1 b2 = 
    let res = compare b1.start_addr b2.start_addr in
    if res = 0 then (
      compare b1.context b2.context
    )else res
end)

(* A modified Tarjan algorithm to find a good weak topological ordering for 
   a graph *)
let head_until x l = 
  if get_log_level IteratorLL = Debug then Format.printf "Entering head_until with a list of size %d\n" (List.length l);
  let rec rev_head_until acc x = function
    [] -> failwith "Head_until called with a list not containing the element\n"
  | y::l -> if x==y then acc else rev_head_until (y::acc) x l
  in List.rev (rev_head_until [] x l)

type graph_visit_tag = NotSeen | Visit of int | Visited
type 'a tarjan = {
  head : int; (*head of the current stronlgy connected componenet *)
  tags : graph_visit_tag BlockMap.t; (*tags the graph to recognize back edges *)
  counter : int; (* a fresh counter, always increased *)
  seen : basicblock list; (* list of blocks seen and not yet put in the wto *)
  wto  : 'a wto (* the result *)
}

(* visit assumes that BlockMap.find b num is NotSeen *)
(* counter is the number of the current block
   b is the current block
   wto is the weak topological ordering computed for the blocks already treated
       (they all come after the current stronlgy connected component)
   num is the tags associated to all blocks in the cfg
   seen is the list of all non treated and seen blocks, in reverse order
        of appearance *)
let rec visit counter num seen b wto =
  if get_log_level IteratorLL = Debug then Format.printf "Visit %d" counter;
  (* First recursively visit the children *)
  (* loop is there to detect if b is in a loop *)
  let state, loop = List.fold_left (fun (s,l) cb -> 
      (match BlockMap.find cb s.tags with
        Visited -> s,l
      | Visit n -> 
          if n <= s.head then {s with head=n}, true
          else s,l
      | NotSeen -> 
          let s' = visit s.counter s.tags s.seen cb s.wto in
          if s'.head<=s.head then s',true else {s' with head = s.head}, l
      ))  ({ head = counter;
            tags = BlockMap.add b (Visit counter) num;
            counter = counter + 1;
            seen = b::seen;
            wto = wto;
          }, false) b.out_edges in
  (* if the current block is the head of the strongly connected
     component, we can treat the block, otherwise we just return the
     state *)
  if counter = state.head then (
    if get_log_level IteratorLL = Debug then Format.printf "Block number %d is the head of its SCC\n" counter;
    let tags = BlockMap.add b Visited state.tags in 
    (* the head of block will be added to the wto *)
    if loop then (
      if get_log_level IteratorLL = Debug then Format.printf "Loop treatment \n";
      let blocks_in_loop = head_until b state.seen in (*all elements except the head*)
      if get_log_level IteratorLL = Debug then Format.printf "head_until passed \n";
      let ctags = List.fold_left (fun tg bl -> BlockMap.add bl NotSeen tg) 
                  tags blocks_in_loop in
      let new_state = component state.counter ctags seen b in
      { new_state with head = state.head;
                       wto = SubWto {
                          head_invariant = Bot;
                          head_block = b;
                          inner_wto =  new_state.wto;
                          next_wto = state.wto;
			  unroll_count = !unroll_count
                       } 
      }
    ) else { state with tags = tags;
                      seen = seen;
                      wto = Linear(b, state.wto) 
         }
  ) else state

(* the final wto of component does not contain the block it is called with *)
and component counter num seen b =
  if get_log_level IteratorLL = Debug then Format.printf "component of block number %d \n" counter;
  List.fold_left (fun s cb ->
      match BlockMap.find cb s.tags with
        NotSeen -> visit s.counter s.tags s.seen cb s.wto
      | _ -> s
      ) { head = 0; (* not used in component *)
          tags = num;
          counter = counter;
          seen = seen;
          wto = EmptyWto;
        } b.out_edges 

(* tarjan cfg takes a cfg and returns a weak topological ordering on the cfg *)
let tarjan cfg =
  let tags = List.fold_left (fun n b -> BlockMap.add b NotSeen n) 
      BlockMap.empty cfg in
  (visit 0 tags [] (List.hd cfg) EmptyWto).wto

(* Changes the unroll values so that the outer loops are not unrolled *)
let rec dont_unroll_outer = function
  Linear(b,w2) -> Linear(b,dont_unroll_outer w2)
| SubWto i -> SubWto{i with unroll_count = 0;
                            next_wto = dont_unroll_outer i.next_wto}
| EmptyWto -> EmptyWto

module Make(A:ArchitectureAD.S) = struct
  
  let print fmt bm = BlockMap.iter (fun b env -> 
      Format.fprintf fmt "@;@[Incoming block %a@; %a@]" pp_block_header b A.print env)
      bm

  open X86Types

  (* binary operations on possibly bottom elements for the domain C *)
  let widen x y = match x with
    Bot -> y
  | Nb x -> A.widen x y

  let subseteq x y = match y with
    Bot -> false
  | Nb y -> A.subseteq x y

  let op32_one = ((X86Types.Imm Int64.one):op32)

  let read_and_interpret_instruction inv (addr, inst) = 
    let newInv = A.read_instruction inv addr in
    (* interpret_instruction interpret the effect of all non jump instructions over
    * an incoming non-bottom environment *)
    (* may raise Bottom *)
    let rec interpret_instruction inv (addr, inst) = try (
      let ftrace inv2 = match get_log_level IteratorLL with
        | Quiet -> instructions_interpreted := !instructions_interpreted + 1;
                   Format.printf "\r %6d instructions interpreted%! %a" !instructions_interpreted (A.print_delta inv) inv2; inv2
        | Normal -> Format.printf "@[<v 2>%a %a @, %a@]@."
               pp_block_addr addr X86Print.pp_instr inst (A.print_delta inv) inv2; inv2
        | Debug -> Format.printf "@[<v 0>@[<v 2>%a %a @, %a@]@;@;#######################@;@;@;@;@]@."
               pp_block_addr addr X86Print.pp_instr inst (A.print_delta inv) inv2;
               inv2 in
      match inst with
        Arith(op, x, y) -> ftrace (
          match op with
            CmpOp -> A.flagop inv (ADcmp(x,y))
          | _ -> A.memop inv (ADarith op) x y
        )
      | Arithb(op, x, y) -> ftrace (
              match op with
                CmpOp -> failwith "8-bit CMP not implemented"
              | _ -> A.memopb inv (ADarith op) x y
        )
      | Cmp(x, y) -> ftrace (A.flagop inv (ADcmp(x,y)))
      | Test(x, y) -> ftrace (A.flagop inv (ADtest(x,y)))
      | Inc x -> interpret_instruction inv (addr,Arith(Add, x, op32_one)) (*TODO: check that the effect on flags is correct *)
      | Dec x -> interpret_instruction inv (addr,Arith(Sub, x, op32_one))
      | Lea(r,a) -> ftrace (A.load_address inv r a)
      | Leave -> 
          let inv = interpret_instruction inv (addr,Mov(Reg ESP, Reg EBP)) in
          interpret_instruction inv (addr,Pop(Reg EBP))
      | Mov(x,y) -> ftrace (A.memop inv ADmov x y)
      | Movb(x,y) -> ftrace (A.memopb inv ADmov x y)
      | Movzx(x,y) -> ftrace (A.movzx inv x y)
      | Exchange(x,y) -> ftrace (A.memop inv ADexchg (Reg x) (Reg y))
      (*
      (* DIV (unsigned divide): makes (1) EAX = EAX / operand;
                                      (2) EDX = EAX % operand;
        we translate it into EDX = EAX; EAX /= operand; EDX %= operand *)
      | Div x -> 
        let inv = interpret_instruction inv (addr,Mov(Reg EDX, Reg EAX)) in
        let inv = interpret_instruction inv (addr,Arith(ADiv, Reg EAX,x)) in
        interpret_instruction inv (addr,Arith(ARem, Reg EDX,x))
      *)
      | Pop x -> ftrace (A.stackop inv ADpop x)
      | Push x -> ftrace (A.stackop inv ADpush x)
      | Shift(op,x,y) -> ftrace (A.shift inv op x y)
      | Halt -> if get_log_level IteratorLL <> Quiet then 
              Format.printf "Just before Halt, we have %a\n" A.print inv;
              raise Bottom
      | Skip -> ftrace (A.elapse inv time_skip)
      | FlagSet(f,b) -> ftrace (A.flagop inv (ADfset(f,b)))
      | Call _ | Jcc _ | Jmp _ | _ -> failwith "Jump instruction in interpret_instruction\n"
      ) with e -> (Format.fprintf Format.err_formatter "@[<v 2>Error while processing %a %a @, in environment %a@]@."
          pp_block_addr addr X86Print.pp_instr inst A.print inv;
          raise e) in
    interpret_instruction newInv (addr, inst)


  let find_out_edge oe x = List.find (fun bo -> bo.start_addr = x) oe

  (* for a given (int,inv) finite_set representing jump targets and
     invariants, return the list of corresponding (basic blocks, invariant) *)

  let out_invs oe = function
    | Top inv -> List.map (fun oe -> oe,inv) oe
    | Finite output ->
      List.fold_left (fun res (ad,ad_inv) -> 
        (try (find_out_edge oe ad, ad_inv)::res
         with Not_found -> res) ) [] output
  
  (* returns a list of out_edges * non-empty env for that edge *)
  let interpret_block inv b = 
    if !trace then Format.printf "Entering block %a@\n" pp_block_header b;
    try (
    let last_inv = List.fold_left 
      (fun inv a -> read_and_interpret_instruction inv a) inv b.content in
    match b.out_edges with
      [] -> assert(b.content = []);[] (*we only have error and final blocks that don't have out edges. TODO: treat the Halt instruction... *)
    | [oe] -> (match b.jump_command with
        None -> [oe,last_inv]
      | Some(Jmp _) ->
        [oe,A. elapse last_inv time_jmp]
      | Some(Call addr) ->
          out_invs b.out_edges (A.call last_inv addr b.next_block_addr)
      | Some Ret -> out_invs b.out_edges (A.return last_inv)
      | Some(Jcc _) -> failwith "Jcc with only one out-going edge"
      | Some _ -> failwith "Jump command is not one of CALL or JMP or JCC"
      )
    | _ -> (match b.jump_command with
      | Some(Call addr) ->
          out_invs b.out_edges (A.call last_inv addr b.next_block_addr)
      | Some(Jmp addr) -> 
          out_invs b.out_edges (A.get_vals (A.elapse last_inv time_jmp) addr)
      | Some(Jcc((truth,cond),ad)) -> ( try 
          let inv_true, inv_false = A.test last_inv cond in
          let next_b = find_out_edge b.out_edges b.next_block_addr
          and jump_b = find_out_edge b.out_edges (Int64.to_int ad) in
          let case_false = match inv_false with
            Bot -> []
          | Nb inv_false -> 
              [(if truth then next_b else jump_b), 
               (A.elapse inv_false time_jmp)] in
          ( match inv_true with 
            Bot -> case_false
          | Nb inv_true ->  
              ((if truth then jump_b else next_b), A.elapse inv_true time_jmp)
                ::case_false
          )
          with Not_found -> failwith "Out edges don't match conditional jump\n"
          | e -> Format.printf "@[Error while processing %a %a @, in environment %a@]@." pp_block_addr b.end_addr X86Print.pp_instr (Jcc((truth,cond),ad)) A.print last_inv;
             raise e)
      | Some Ret -> out_invs b.out_edges (A.return last_inv)
      | _ -> failwith "Jump command inconsistent with the number of out edges\n"
      )
    ) with Bottom -> []
          
    
  type environment = A.t BlockMap.t (* collected initial invariants of blocks *)

(* env_add b binv env joins the invariant inv to b in env, which are supposed to
 * be non-bottom *)
  let env_add b binv env =
    let inv = try 
      let env1 = BlockMap.find b env in
      if !trace then Format.printf "@[Joining incoming envs for %a "
        pp_block_header b;
      let res = A.join env1 binv in
      if !trace then Format.printf " gives %a@]" (A.print_delta env1) res;
      res
    with Not_found -> binv in
    BlockMap.add b inv env

(*env_remove pb b env removes b from env if it is not in the set of precious blocks, pb *)
  let env_remove pb b env =
    if List.mem b pb then env else BlockMap.remove b env

  let iterate concr_mem start_values data_cache_params inst_cache_params inst_base_addr cfg =
    if get_log_level IteratorLL <> Quiet then trace:= true;
    if get_log_level IteratorLL = Debug then Format.printf "CFG of %d blocks \n" (List.length cfg);
    let start_block = List.hd cfg in
    let final_blocks = List.filter (fun b -> b.out_edges = []) cfg in
    (* init_env and env below map blocks to their incoming non-empty abstract
     * environments *)
    let init_env = BlockMap.singleton start_block (A.init concr_mem start_values data_cache_params inst_cache_params inst_base_addr) in
    if !trace then Format.printf "@[Initially, %a@]@." print init_env;
    let wto = tarjan cfg in
    let wto = if !unroll_outer_loop then wto else dont_unroll_outer wto in
    if get_log_level IteratorLL = Debug then Format.printf "@[Iteration ordering is %a@.@]" pp_wto wto;
    (* TODO: Explain the role of pb *)
    let rec next_i pb env = function 
      | EmptyWto -> env
      | Linear(b,w) -> 
	(* If block b has an incoming environment, interpret b, remove
	   incoming environment from b and update incoming environments
	   of all blocks affected by b's outcoming environment. 
	   Continue interpretation with next block w*)
	      if BlockMap.mem b env then
          let in_inv = BlockMap.find b env in
	  (* out_invs : (Cfg.basicblock * A.t) list *)
          let out_invs = interpret_block in_inv b in
          next_i pb (List.fold_left (fun e (ob,oinv) -> env_add ob oinv e) 
		       (env_remove pb b env) out_invs) w
        else ( if !trace then Format.printf "Block %a with empty incoming env is
        ignored.@." pp_block_addr b.start_addr; 
               next_i pb env w)
      | SubWto it -> 
        (* First check for fixpoint *)
        if BlockMap.mem it.head_block env then
          let incoming_inv = BlockMap.find it.head_block env in
          if subseteq incoming_inv it.head_invariant then ( 
            if !trace then Format.printf "Local fixpoint reached for %a\n"
              pp_block_header it.head_block;
	    next_i pb (env_remove pb it.head_block env) it.next_wto
	  )
	  else(
	  let unroller=it.unroll_count in
	  (* Case 1: Unroll for unroll_count times *)
	  if unroller > 0 then (
	    let ur_inv = next_i pb env (Linear(it.head_block, it.inner_wto)) in
            next_i pb ur_inv (SubWto{ it with unroll_count = unroller-1;})
	  )
	  (* Case 2: Compute fixpoint using widening:
	     check whether incoming environment is subset of
	     head invariant. If yes, fixpoint reached; continue interpretation w/ next wto
	     If not, apply widening to head invariant and incoming invariant
	  *)
	  else(
            if !trace then Format.printf "Iteration over block %a\n"
              pp_block_header it.head_block;
            let w_inv = widen it.head_invariant incoming_inv in
            if !trace then (match it.head_invariant with 
	      | Bot -> ()
              | Nb inv1 -> Format.printf "@[<2>Widening of @.--1-- %a @.and --2-- %a @.gives --1v2-- %a@]"
		A.print inv1
		A.print incoming_inv
		A.print w_inv
            );
	    let it_env = next_i (it.head_block::pb )
              (BlockMap.add it.head_block w_inv env) 
              (Linear(it.head_block, it.inner_wto)) in
            next_i pb it_env (SubWto{ it with head_invariant = Nb w_inv;})
          ))
        else (* We arrive with an empty environment.
        * But maybe some inner blocks of that loop have non-empty incoming envs, so we iterate at least once *)
          let env1 = next_i pb env it.inner_wto in
          if BlockMap.mem it.head_block env1 then next_i pb env1 (SubWto it)
          else (
            if !trace then Format.printf "Loop starting at block %a with empty incoming env.@." pp_block_addr it.head_block.start_addr; 
            next_i pb env it.next_wto
          )
    in
    let final_env = next_i final_blocks init_env wto in
    print Format.std_formatter final_env
end
