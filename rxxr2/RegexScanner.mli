(* © Copyright University of Birmingham, UK *)

(* scan result *)
type result =
  |Eof
  |Error of exn * string
  |Regex of Nfa.t * string;;

(* internal regex scanner type *)
type t;;

(* create a new regex scanner from the specified file *)
val make : string -> t;;

(* return the next regex on file *)
val next : t -> result;;
