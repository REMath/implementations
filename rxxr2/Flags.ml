(* © Copyright University of Birmingham, UK *)

type t = int;;

let empty = 0;;
let interrupted = 1;;
let accepting = 2;;
let klnhit = 4;;
let eoihit = 8;;
let pruned = 16;;

let is_empty f = (f = 0);;
let is_interrupted f = (f land interrupted) != 0;;
let is_accepting f = (f land accepting) != 0;;
let is_klnhit f = (f land klnhit) != 0;;
let is_eoihit f = (f land eoihit) != 0;;
let is_pruned f = (f land pruned) != 0;;

let set_interrupted f = f lor interrupted;;
let set_accepting f = f lor accepting;;
let set_klnhit f = f lor klnhit;;
let set_eoihit f = f lor eoihit;;
let set_pruned f = f lor pruned;;

let union f1 f2 = f1 lor f2;;
