(* © Copyright University of Birmingham, UK *)

open Common

(* internal representation of the analyser *)
type t;;

(* initialize analyser instance for the given (x, phi) and the pumpable kleene *)
val init : (Nfa.t * Word.t * Phi.t) -> (int * IntSet.t) -> t;;

(* calculate the next (y1, triple) *)
val next : t -> (Word.t * Triple.t) option;;

(* read current analyser flags *)
val flags : t -> Flags.t;;
