(* © Copyright University of Birmingham, UK *)

open Common

(* internal representation of beta *)
type t;;

module BetaSet : (Set.S with type elt = t);;

(* beta with just one state *)
val make : int -> t;;

(* returns the set of states contained within this beta *)
val elems : t -> IntSet.t;;

(* calculate all one-character reachable betas *)
val advance : (Nfa.t * Word.t * t) -> (Word.t * t) list;;

(*
  - consume all epsilon transitions while recording pumpable kleene encounters
  - for each pumpable kleene found, returns the corresponding left-beta (everything
    upto the kleene state)
  - also returns the final evolved beta
*)
val evolve : (Nfa.t * Word.t * t) -> IntSet.t -> Flags.t * t * (int * t) list;;
