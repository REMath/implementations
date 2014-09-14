(* © Copyright University of Birmingham, UK *)

open Common

(* internal representation of the analyser *)
type t;;

(* initialize analyser instance for the specified triple and the kleene state *)
val init : (Nfa.t * Word.t * Triple.t) -> int -> t;;

(* calculate the next (y2, phi) *)
val next : t -> (Word.t * Phi.t) option;;

(* read analyser flags *)
val flags : t -> Flags.t;;
