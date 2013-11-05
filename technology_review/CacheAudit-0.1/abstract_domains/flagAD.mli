(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)


open X86Types
open AbstractInstr
open AD.DS
open NumAD.DS

(** Flag abstract domain: keeps track of the relationship of flags and
    variable values. Currently restricted to combinations of CF and
    ZF) *)

module type S = 
sig
  include AD.S

  (** Initializes an empty FlagAD by specifying how variable names
      are printed *)
  val init : (var->string) -> t

  (** Create new variable *)
  val new_var : t -> var -> t

  (** Delete variable *)
  val delete_var : t -> var -> t

  (** Log the current values of a variable to the log file. For automated testing *)
  val log_var : t -> var -> unit

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

  (** Meet operation *)
  val meet : t -> t -> t 

  (** [update_var env dst mskdst src msksrc op] performs operation
      [op] on [dst] and [src], where the masks [mskdst] and [msksrc]
      specify whether 8 or 32 bit of the operand are involved. *)
  val update_var : t -> var -> mask -> cons_var -> mask -> varop -> t
    
  (** Returns a pair of environments overapproximating the
      true/false cases of condition *)
  val test : t -> condition -> (t add_bottom)*(t add_bottom)

  (** [flagop env op var1 var2] performs [op] between [var1] and
      [var2]. *)
  val flagop : t -> cons_var flagop -> t
 
  (** [shift env op dst src msk] performs [op] between [src] and
      [dst].*)
  val shift : t -> shift_op -> var -> cons_var -> mask -> t
end

(** Creates a flag abstract domain from a numeric abstract domain *)
module Make :
  functor (V : NumAD.S) -> S
