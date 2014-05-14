(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(** Module for creating and printing control flow graphs *)

(** Type for basic blocks. A final jump command is stored in
    [jump_command] and is not contained in the block's content *)
type basicblock = {
  start_addr : int;
  end_addr : int;
  next_block_addr : int;
  content : (int * X86Types.instr) list;
  jump_command : X86Types.instr option;
  context : int list;
  mutable out_edges : basicblock list;
  mutable in_edges : basicblock list;
}

(** Type for control flow graphs *)
type t=basicblock list

(** Creates control flow graph from a given starting address in the binary executable (typically: [main]) *)
val makecfg : int -> X86Headers.t -> t

(** Prettyprinter for basic block addresses *)
val pp_block_addr : Format.formatter -> int -> unit

(** Prettyprinter for basic block headers *)
val pp_block_header : Format.formatter -> basicblock -> unit

(** Prettyprinter for basic block content *)
val pp_block : Format.formatter -> basicblock -> unit

(** Prettyprinter for the entire control flow graph *)
val printcfg : t -> unit
