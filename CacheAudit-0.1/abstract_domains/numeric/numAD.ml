(* Copyright (c) 2013, IMDEA Software Institute.              *)
(* See ../../LICENSE for authorship and licensing information *)

(** The base type of the numeric abstract domains used in CacheAudit *)
open X86Types
open AD.DS

(** Module containing data structures common to numeric abstract domains *)
module DS = struct

  (** Type of variables *)
  type var = Int64.t
      
  (** Type for numeric operands, which can be either variables or numeric constant *)
  type cons_var = Cons of int64 | VarOp of var

  (** Converts cons_var to var *)
  let consvar_to_var = function (* TODO: Rename to operand_to_var? *)
    | VarOp x -> x
    | Cons _ -> failwith "consvar_to_var: can't convert constant"


  (** Types for masking operations *)
  type mask_t = HH | HL | LH | LL
  type mask = NoMask | Mask of mask_t

  let rem_to_mask = function
    | 0L -> HH
    | 1L -> HL
    | 2L -> LH
    | 3L -> LL
    | _ -> failwith "rem_to_mask: incorrect offset"

  let mask_to_intoff = function
    | HH -> (0xFF000000L, 24)
    | HL -> (0x00FF0000L, 16)
    | LH -> (0x0000FF00L, 8)
    | LL -> (0x000000FFL, 0)

  (**/**) (* Definitions below are not included in documentation *)

  module NumSet = Set.Make(Int64)
  module NumMap = Map.Make(Int64)
  module IntSet = Set.Make(struct type t = int let compare = compare end)
  module IntMap = Map.Make(struct type t = int let compare = compare end)
  module VarMap = Map.Make(struct type t=var let compare = compare end)

end

open DS

module type S = sig 
  include AD.S

  (** Initializes an empty numeric AD by specifying how variable names
      are printed *)
  val init : (var->string) -> t

  (** Create new variable *)
  val new_var : t -> var -> t

  (** Delete variable *)
  val delete_var : t -> var -> t

  (** Log the current values of a variable to the log file. For automated testing *)
  val log_var : var -> t -> unit

  (** [get_var env var] returns the current values of a variable
      [var], in form of a Map from values of [var] to environments in
      which [var] has that value. This interface can be used to
      capture relational information between variables (but could be
      substituted by a simpler/more efficient one for non-relational
      domains) *)
  val get_var : t -> var -> (t NumMap.t) add_top

  (** [set_var env var l h] sets the value of [var] to be in the
      interval [l,h] *)
  val set_var : t -> var -> int64 -> int64 -> t

 (** Checks if a variable is represented by the domain *)
  val is_var : t -> var -> bool

  (** Returns the variables represented by the domain *)
  val var_names : t -> NumSet.t

  (** Meet operation *)
  val meet : t -> t -> t add_bottom 

  (** [update_var env dst mskdst src msksrc op] performs operation
      [op] on [dst] and [src], where the masks [mskdst] and [msksrc]
      specify whether 8 or 32 bit of the operand are involved. Returns
      one environment per value combination of CF and ZF. *)
  val update_var : t -> var -> mask -> cons_var -> mask -> AbstractInstr.varop ->
    (t add_bottom)*(t add_bottom)*(t add_bottom)*(t add_bottom) 
  (* This interface should be changed to allow flags as argument and
      return a tree *)

 
  (** [flagop env op var1 var2] performs [op] between [var1] and
      [var2]. Returns one environment per value combination of CF and
      ZF *)
  val flagop : t -> arith_op -> cons_var -> cons_var ->
    (t add_bottom)*(t add_bottom)*(t add_bottom)*(t add_bottom)
      
  (** [shift env op dst src msk] performs [op] between [src] and
      [dst]. Returns one environment per value combination of CF and
      ZF *)
  val shift : t -> shift_op -> var -> cons_var -> mask ->
    (t add_bottom)*(t add_bottom)*(t add_bottom)*(t add_bottom)
 
end

