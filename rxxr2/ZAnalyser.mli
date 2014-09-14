(* © Copyright University of Birmingham, UK *)

open Common

(* internal representation of the analyser *)
type t;;

(* initialize analyser instance for the specified (xy, phi) *)
val init : (Nfa.t * Word.t * Phi.t) -> t;;

(* calculate the next (z, phi) *)
val next : t -> (Word.t * Phi.t) option;;

(* read analyser flags *)
val flags : t -> Flags.t;;
