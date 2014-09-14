(* © Copyright University of Birmingham, UK *)

open Common

(* internal representation of phi *)
type t;;

module PhiSet : (Set.S with type elt = t);;

(* convert a set of states into a phi *)
val make : IntSet.t -> t;;

(* extract elements of phi *)
val elems : t -> IntSet.t;;

(* compare two phis *)
val compare : t -> t -> int;;

(* check if the first phi is a subset of the second *)
val subset : t -> t -> bool;;

(* formatting a phi for output *)
val print : t -> string;;

(* compute all single-character (or class) reachable phis *)
val advance : (Nfa.t * Word.t * t) -> (Word.t * t) list;;

(* advance phi, also look for characters which can fail the entire phi *)
val explore : (Nfa.t * Word.t * t) -> (Word.t * t) list * (char * char) list;;

(* consume all epsilon moves, optionally check for a kleene encounter *)
val evolve : (Nfa.t * Word.t * t) -> int option -> (Flags.t * t);;

(* simulate phi against the provided input *)
val simulate : (Nfa.t * Word.t * t) -> char list -> (Flags.t * Word.t * t);;
