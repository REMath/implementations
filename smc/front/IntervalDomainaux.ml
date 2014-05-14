(* Heuristics for interval widening *)

open BinPos
open BinNums
open BinInt
open Camlcoq
open Integers

let rec next_pow2_pos = function
  | Coq_xI p0 -> Coq_xI (next_pow2_pos p0)
  | Coq_xO p0 -> Coq_xI (next_pow2_pos p0)
  | Coq_xH -> Coq_xH
    
let previous_pow2_pos p =
  let p' = next_pow2_pos p in
  (match p' with
    | Coq_xI p0 -> p0
    | _ -> p')

let next_threshold (z : coq_Z) = 
  match z with
    | Z0 -> Z0
    | Zpos Coq_xH -> Zpos Coq_xH
    | Zneg Coq_xH -> Zneg Coq_xH
    | Zpos p -> Zpos (next_pow2_pos p)
    | Zneg p -> Zneg (previous_pow2_pos p)

let previous_threshold (z : coq_Z) = 
  match z with
    | Z0 -> Z0
    | Zpos Coq_xH -> Zpos Coq_xH
    | Zneg Coq_xH -> Zneg Coq_xH
    | Zpos p -> Zpos (previous_pow2_pos p)
    | Zneg p -> Zneg (next_pow2_pos p)

exception Found of coq_Z

let next_larger (z : coq_Z) : coq_Z =
  let next_t = next_threshold z in
    next_t

let next_smaller (z : coq_Z) : coq_Z =
  let previous_t = previous_threshold z in
    previous_t

