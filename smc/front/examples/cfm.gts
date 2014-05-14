(*  0 *) goto main
(*  2 *) cst 7 -> R0
(*  4 *) goto 12
(*  6 *) main:
(*  7 *) cst 15 -> R1
(*  9 *) load *R1 -> R2
(* 10 *) cst -7 -> R0
(* 12 *) add R0 -> R2
(* 13 *) store R2 -> *R1
(* 14 *) goto dead
(* 16 *) dead:
