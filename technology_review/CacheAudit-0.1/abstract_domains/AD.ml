(* Copyright (c) 2013, IMDEA Software Institute.             *)
(* See ../LICENSE for authorship and licensing information   *)

(** The base type of all abstract domains used in CacheAudit *)

module type S = sig 
  type t

(** Join operator *)
  val join: t -> t -> t

(** Widening operator *)
  val widen: t -> t -> t


(** Test for inclusion. true means that gamma(x) is
      contained in gamma(y); false means that we could not infer this fact *)
  val subseteq: t -> t -> bool

(** Prints the current state *)
  val print : Format.formatter -> t -> unit

(** Prints the delta between two states. Needed for outputting execution traces *)
  val print_delta : t -> Format.formatter -> t -> unit
end

(** Module containing common data structures useful for abstract domains *)
module DS = struct
  
  (** Type of finite sets of couples, Top when the set is too big *)
  type ('a,'b) finite_set = Finite of ('a*'b) list | Top of 'b
  
  (** Adding a top element Tp to an abstract domain *)
  type 'a add_top = Nt of 'a | Tp
  exception TopException

  (** Adding a bottom element to an abstract domain *)
  type 'a add_bottom = Nb of 'a | Bot
  exception Bottom

  (** Lifting a function f on two domains without bottom when bottom should be absorbed *)
  let lift_combine f a1 a2 = match a1,a2 with
    Bot, x | x, Bot -> x
  | Nb x1, Nb x2 -> Nb(f x1 x2)

end
