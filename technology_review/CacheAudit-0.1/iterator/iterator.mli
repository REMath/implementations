(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(** An iterator module for analysis of executables. Based on "Efficient Chaotic Iteration Strategies With Widenings" by F. Bourdoncle *)

(** The number of times each loop is unrolled before widening is applied. Default = 100. *)
val unroll_count : int ref

(** Include outermost loop in unrolling. Default = true. *)
val unroll_outer_loop : bool ref


module Make :
  functor (A : ArchitectureAD.S) ->
    sig
      (** Performs fixpoint computation. Takes as arguments an
	  executable (represented by [X86Headers.t]), initialization
	  options for the memory, data cache, (optional) instruction
	  cache, and a control flow graph. *)
      val iterate :
        X86Headers.t -> 
        MemAD.mem_param ->
        CacheAD.cache_param ->
        CacheAD.cache_param option -> int64 -> 
	Cfg.basicblock list -> unit
    end
