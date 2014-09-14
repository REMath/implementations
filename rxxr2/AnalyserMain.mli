(* © Copyright University of Birmingham, UK *)

open Common

(* enumerate all the attack strings, even partial ones *)
val enumerate_verbose : Nfa.t -> unit;;

(* normal exhaustive search for an attack string *)
val search_exhaustive : Nfa.t -> (Word.t * Word.t * Word.t) option;;

(* optimized search with pruning *)
val search_optimized : Nfa.t -> int -> Flags.t * IntSet.t * (int * Word.t * Word.t * Word.t) option;;
