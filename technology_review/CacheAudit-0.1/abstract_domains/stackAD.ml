(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

open X86Types
open AbstractInstr
open AD.DS

module type S = 
  sig
    include AD.S

    val init : X86Headers.t -> MemAD.mem_param -> CacheAD.cache_param -> t
    val get_vals : t -> op32 -> (int, t) finite_set
    val test : t -> condition -> t add_bottom * t add_bottom
    val call : t -> op32 -> int -> (int, t) finite_set
    val return : t -> (int, t) finite_set
    val memop : t -> memop -> op32 -> op32 -> t
    val memopb : t -> memop -> op8 -> op8 -> t
    val movzx : t -> op32 -> op8 -> t
    val load_address : t -> reg32 -> address -> t
    val flagop : t -> op32 flagop -> t
    val stackop : t -> stackop -> op32 -> t
    val shift : t -> shift_op -> op32 -> op8 -> t
    val touch : t -> int64 -> t
    val elapse : t -> int -> t
  end


(* Simple stack abstract domain. Translates pushs and pops to register operations *)

module Make (M: MemAD.S) = struct
    (* Stack.top and Memory abstract domain *)
  type t = M.t

  let init mem mem_params cache_params = M.init (fun addr -> 
    if addr=Int64.zero then failwith "0 address raises seg fault \n"
    else try Some(X86Headers.lookup mem addr) with 
        (*We then assume it is not initialzed*)
      X86Headers.InvalidVirtualAddress -> None) mem_params cache_params (*TDO check that it falls in the stack *)
  let join = M.join 
  let widen = M.widen 
  let subseteq = M.subseteq 
  let get_vals  = M.get_vals
  let test = M.test
  let memop = M.memop
  let memopb  = M.memopb
  let movzx = M.movzx
  let flagop = M.flagop
  let load_address = M.load_address
  let shift = M.shift
  let top_stack =  Address {  addrDisp = 0L;
                              addrBase = Some ESP;
                              addrIndex = None;
                              segBase = None;}
  let stackop mem operation gop = 
    match operation with 
      (* POP: return top, *then* increment ESP *)
      | ADpop -> 
	(* Move top of stack to address/register gop *)
	let mem1 = memop mem ADmov gop top_stack in
	(* Increment ESP by 4 -- Stack grows downwards *)
	memop mem1 (ADarith Add) (Reg ESP) (Imm 4L)
	  
      (* PUSH: decrement ESP, *then* store content *)
      | ADpush ->
	(* Decrement ESP by 4 *)
	let mem1 = memop mem (ADarith Sub) (Reg ESP) (Imm 4L) in
	(* Move gop to top of stack *)
	memop mem1 ADmov top_stack gop
	 

   (* Notice: We push/pop offsets to the stack, not absolute addresses.*) 
  let call mem tgt ret =  
    (* push target address to stack *)
    let mem1 = stackop mem ADpush (Imm (Int64.of_int ret))
    (* return list of possible call targets and their environments *)
    in get_vals mem1 tgt 
 
  let return mem = 
   (* Return top of stack and increment ESP by 4. We do not reuse
      the stackop function because POP stores its value in an
      op32 *)
    let mem1 = memop mem (ADarith Add) (Reg ESP) (Imm 4L) in
    get_vals mem1 (Address {  addrDisp = -4L;addrBase = Some ESP; addrIndex = None;segBase = None;})
      
     
     
  let print = M.print
  let print_delta = M.print_delta

  (* keep track of time *)
  let elapse = M.elapse

  let touch = M.touch 
end 


