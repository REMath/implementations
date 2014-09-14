(* © Copyright University of Birmingham, UK *)

open Common

(* internal representation of the analyser *)
type t;;

(* initialize analyser instance with the given NFA and the pumpable kleene set *)
val init : Nfa.t -> IntSet.t -> t;;

(* calculate the next (x, phi) corresponding to some pumpable kleene *)
val next : t -> (int * Word.t * Phi.t) option;;

(* read current analyser flags *)
val flags : t -> Flags.t;;
