(* © Copyright University of Birmingham, UK *)

(* internal representation of flags *)
type t;;

(* various flags used during the analysis phase *)
val empty : t;;
val interrupted : t;; (* analysis interrupted due to unsupported constructs *)
val accepting : t;; (* accpeting state found *)
val klnhit : t;; (* kleene found *)
val eoihit : t;; (* end of input anchor found *)
val pruned : t;; (* analysis pruned *)

(* functions for querying flags *)
val is_empty : t -> bool;;
val is_interrupted : t -> bool;;
val is_accepting : t -> bool;;
val is_klnhit : t -> bool;;
val is_eoihit : t -> bool;;
val is_pruned : t -> bool;;

(* functions for setting flags *)
val set_interrupted : t -> t;;
val set_accepting : t -> t;;
val set_klnhit : t -> t;;
val set_eoihit : t -> t;;
val set_pruned : t -> t;;

(* flag union *)
val union : t -> t -> t;;
