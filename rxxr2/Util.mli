(* © Copyright University of Birmingham, UK *)

open Common

(* check epsilon reachability, word argument is used for evaluating predicates only *)
val is_epsilon_reachable : Nfa.t -> Word.t -> int -> int -> bool;;

(* find pumpable kleene nodes, along with the corresponding branch points *)
val find_pumpable_kleene : Nfa.t -> (int, IntSet.t) Hashtbl.t;;
