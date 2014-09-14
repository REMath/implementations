(* © Copyright University of Birmingham, UK *)

open Common

(* internal product representation *)
type t;;

module ProductSet : (Set.S with type elt = t);;

(* make a new product with an NFA state and a phi *)
val make : int -> Phi.t -> t;;

(* extract elements of a product *)
val elems : t -> (int * Phi.t);;

(* calculate all single-character (or class) reachable products *)
val advance : (Nfa.t * Word.t * t) -> (Word.t * t) list;;

(* 
  - consume all the epsilon moves while looking for branch points
  - spawns a triple for each branch point
*)
val evolve : (Nfa.t * Word.t * t) -> IntSet.t -> Flags.t * t * Triple.t list;;
