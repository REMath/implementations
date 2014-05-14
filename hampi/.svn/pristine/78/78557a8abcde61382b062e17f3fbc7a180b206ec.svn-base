open Cfg ;;
open Basics ;;

val unique_symbols                             : alphabet -> int -> int -> constraints
val composition_topdown                        : fullCFG -> int -> int -> constraints
val composition_bottomup                       : fullCFG -> int -> int -> constraints
(*
val closure_topdown                            : fullCFG -> int -> int -> constraints
val closure_bottomup                           : fullCFG -> int -> int -> constraints
*)
val derivable                                  : fullCFG -> int -> int -> constraints 
val underivable                                : fullCFG -> int -> int -> constraints 
(*
val base_topdown                               : fullCFG -> int -> int -> constraints 
val base_bottomup                              : fullCFG -> int -> int -> constraints 
*)
val derives_one_but_not_the_other              : int -> int -> constraints 
val derives_one_but_not_the_other_implications : fullCFG -> fullCFG -> int -> int -> constraints 
val derives_exactly_one                        : int -> int -> constraints
val derives_exactly_one_implications           : fullCFG -> fullCFG -> int -> int -> constraints
val all_derivable                              : int -> int -> constraints 
val all_derivable_implications                 : fullCFG list -> int -> int -> constraints 
val two_productions                            : fullCFG -> int -> int -> constraints

(*
val ambiguity_base                             : fullCFG -> int -> int -> constraints
val ambiguity_derivable                        : fullCFG -> int -> int -> constraints
val ambiguity_closure                          : fullCFG -> int -> int -> constraints
val ambiguity_composition                      : fullCFG -> int -> int -> constraints
*)





(*
val retrieve_derived_word   : fullCFG -> int -> int -> string
val retrieve_underived_word : fullCFG -> int -> int -> string
*)
