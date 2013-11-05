(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

open X86Types
open AbstractInstr
open AD.DS

(** Memory abstract domain: maps machine operations to operations on integer variables *)

(** List of initial values for registers. Register * lower bound * upper bound *)
type reg_init_values = (X86Types.reg32 * int64 * int64) list

(** List of initial values for memory addresses. Adress * lower bound * upper bound *)
type mem_init_values = (int64 * int64 * int64) list

(** Parameters for the Memory Abstract Domain initialization *)
type mem_param = mem_init_values * reg_init_values

module type S =
sig
  include AD.S
    
 (** Creates a MemAD with given parameters. More specifically, in 
      [init iv mem dcp]     
       - [iv] represents initial values of memory locations
       - [mem] are initial values of registers
       - [dcp] is the configuration of the data cache, and
  *)
  val init: (int64 -> int64 option) -> mem_param -> CacheAD.cache_param -> t
    
 (** [get_vals env op] returns a finite list of possible values for an op32 
      operand (which is an register/memory address/immediate), and the 
      respective environments.  In case no finite list can be determied, 
      returns Top. *)
  val get_vals: t -> op32 -> (int,t) finite_set

  (** Returns an overapproximation of the environments in which the condition holds,
      followed by an overapproximation of the environments in which it doesn't. *)
  val test : t -> condition -> (t add_bottom)*(t add_bottom)

  (** 32 bit memory operation *)
  val memop : t -> memop -> op32 -> op32 -> t

  (** 8 bit memory operation *)
  val memopb : t -> memop -> op8 -> op8 -> t

  (** Load operation *)
  val load_address : t -> reg32 -> address -> t

  (** Move with zero extend *)
  val movzx : t -> op32 -> op8 -> t

  (** Flag operation *)
  val flagop : t -> op32 flagop -> t

  (** Shift operation *)
  val shift : t -> shift_op -> op32 -> op8 -> t
    
  (** Signals to the cache that a memory location has been accessed *)  
  val touch : t -> int64 -> t

  (** Signals from the iterator to the cache the time
      consumed by an instruction *)
  val elapse : t -> int -> t
end
    
(** Creates a memory abstract domain from a flag and cache abstract domains *)
module Make :
  functor (F : FlagAD.S) ->
    functor (C : CacheAD.S) -> S


(** Appends an address to the list of addresses that are logged.  The
    ordering of values in the log file corresponds to the ordering of
    that list.  Whenever there is a call to print, all addresses are
    logged *)
val log_address: int64 -> unit
