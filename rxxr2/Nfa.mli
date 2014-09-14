(* some grouping constructs are not supported in the NFA format *)
exception UnsupportedGroupingConstruct of int

(* predicates *)
type p = 
  |P_BOI 
  |P_EOI 
  |P_EOIX of bool
  |P_BOL of bool
  |P_EOL of bool
  |P_EOM
  |P_WB
  |P_NWB;;

(* type of states, most states contain a pointer to the next state *)
type s = 
  |End
  |Kill
  |Pass of int (* epsilon *)
  |MakeB of int (* introduce barrier *)
  |EvalB of int (* evaluate barrir *)
  |Match of (char * char) list * int
  |CheckPred of p * int
  |CheckBackref of int * int
  |BeginCap of int * int
  |EndCap of int * int
  |BranchAlt of int * int
  |BranchKln of bool * int * int;;

(* inner type used to represent the NFA *)
type t;;

(* compile a pattern into an NFA *)
val make : ParsingData.pattern -> t;;

(* return root node id *)
val root : t -> int;;

(* return the number of states *)
val size : t -> int;;

(* return the specified state *)
val get_state : t -> int -> s;;

(* return the list of ordered transitions for the specified state *)
val get_transitions : t -> int -> (char * char * int) list;;

(* return sub-expression position in the input string *)
val get_subexp_location : t -> int -> (int * int);;
