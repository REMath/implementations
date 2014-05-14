open Cil_types
open Lexing

(* The type of the detected vulnerability. *)
type vulnerability = FunctionConstraint of stmt * string | BufferIndex of stmt * string 

let extract_loc s = 
      match s.skind with
      | Instr i ->
        (match i with
        | Set (_, _, (loc, _)) -> Some loc
        | Call (_, _, _, (loc, _)) -> Some loc
        | _ -> None
        )
      | _ -> None

let compare v1 v2 = 
  let _compare_locs loc1 loc2 =
    match (loc1, loc2) with
    | (Some loc1, Some loc2) -> 
      (match String.compare loc1.pos_fname loc2.pos_fname with
      | 0 -> loc1.pos_lnum - loc2.pos_lnum
      | x -> x
      )
    | (Some loc1, None) -> -1
    | (None, Some loc2) -> 1
    | (None, None) -> 0
  in
  match (v1, v2) with
  | (FunctionConstraint (s1, _), FunctionConstraint (s2, _)) -> 
    let loc1 = extract_loc s1 in
    let loc2 = extract_loc s2 in
    _compare_locs loc1 loc2  
  | (FunctionConstraint (s1, _), BufferIndex (s2, _)) ->
    let loc1 = extract_loc s1 in
    let loc2 = extract_loc s2 in
    _compare_locs loc1 loc2
  | (BufferIndex (s1, _), FunctionConstraint (s2, _)) ->
    let loc1 = extract_loc s1 in
    let loc2 = extract_loc s2 in
    _compare_locs loc1 loc2
  | (BufferIndex (s1, _), BufferIndex (s2, _)) ->
    let loc1 = extract_loc s1 in
    let loc2 = extract_loc s2 in
    _compare_locs loc1 loc2
