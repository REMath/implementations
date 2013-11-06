open Cfg ;;

type variable = T of (string * int)      
              | T' of (string * int)      
              | N of (fullCFG * string * int * int)
              | H of (fullCFG * string * string * int * int * int)
              | B of int
              | B' of int
              | Two of (string * int * int)
              | One of (string * int * int)
	      | A of (fullCFG * string * int * int)
	      | AO of (string * int * int * int)
	      | AT of (string * int * int * int)
	      | ATH of (string * string * int * int * int)
	      | AOH of (string * string * int * int * int)
(*
              | H12 of (fullCFG * string * string * int * int * int)
              | H21 of (fullCFG * string * string * int * int * int)
	      | A of (fullCFG * string * int * int * int * int)
	      | C of (fullCFG * string * int * int)
	      | D of (fullCFG * string * string * string * string * int * int * int * int)
              | H' of (fullCFG * string * string * string * int * int)
*)

val showVar : variable -> string

val posEncode : variable -> int 
val negEncode : variable -> int 
val getCode   : variable -> int

(* exception Variable_unknown_to_zchaff of string *)

val getValue : variable -> int

val showAllValues : unit -> unit

(*
val getTVar    : string * int -> int
val getNegTVar : string * int -> int
val getNVar    : string * int * int * int -> int
val getNegNVar : string * int * int * int -> int
val getHVar    : string * string * int * int * int -> int
val getNegHVar : string * string * int * int * int -> int
val getBVar    : int -> int
val getNegBVar : int -> int
val getIVar    : int -> int
val getNegIVar : int -> int
val getYVar    : string * int * int * int * int -> int
val getNegYVar : string * int * int * int * int -> int
*)
