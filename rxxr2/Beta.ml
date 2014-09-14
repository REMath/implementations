(* © Copyright University of Birmingham, UK *)

open Common
open Nfa

(* each beta is represented by a simple (reversed) list of states *)
type t = int list;;

module BetaSet = Set.Make (
  struct
    type t = int list;;
    let compare = Pervasives.compare;;
  end);;

let make i = [i];;

let elems b = List.fold_left (fun s i -> IntSet.add i s) IntSet.empty b;;

(* sorted tree of betas *)
type otree = OTNull | OTNode of char * char * int list * otree * otree;;

(*
  - inserts a new beta into the tree
  - in case of overlaps, the new beta is pushed in front of the old one

  - TODO: Not sure if pushing in-front improves performance or not (needs profiling)
  - is this the whole reason for storing beta in reverse ?
*)
let rec otr_add tr _u _v _l = match tr with
  |OTNull -> OTNode (_u, _v, _l, OTNull, OTNull)
  |OTNode (u, v, l, ltr, rtr) when _v < u -> OTNode (u, v, l, otr_add ltr _u _v _l, rtr)
  |OTNode (u, v, l, ltr, rtr) when v < _u -> OTNode (u, v, l, ltr, otr_add rtr _u _v _l)
  |OTNode (u, v, l, ltr, rtr) ->
    let _ltr = if u == _u then ltr else if u < _u then otr_add ltr u (zprev _u) l else otr_add ltr _u (zprev u) _l in
    let _rtr = if v == _v then rtr else if _v < v then otr_add rtr (znext _v) v l else otr_add rtr (znext v) _v _l in
    OTNode (max u _u, min v _v, _l @ l, _ltr, _rtr);;

(* collect the new betas, with the corresponding prefix words leading to them *)
let rec otr_collect tr w lst = match tr with
  |OTNull -> lst
  |OTNode (u, v, l, ltr, rtr) ->
    (* 
      - we must fold right, since the beta is stored in reverse
      - only keep the left-most (right-most when reversed) occurrences using an integer set
    *)
    let (_, b) = List.fold_right (fun i (s, b) -> if IntSet.mem i s then (s, b) else (IntSet.add i s, i :: b)) l (IntSet.empty, []) in
    (* package the resulting beta along with its prefix *)
    otr_collect rtr w (otr_collect ltr w ((Word.extend w (u, v), b) :: lst));;

let advance (nfa, w, b) =
  (*
    - we must fold right, since the beta is stored in reverse
    - otr_add pushes new betas in front of old ones, respecting the reverse order
  *)
  let tr = List.fold_right (fun i tr -> List.fold_left (fun tr (u, v, j) -> otr_add tr u v [j]) tr (Nfa.get_transitions nfa i)) b OTNull in
  otr_collect tr w [];;

let evolve (nfa, w, b) kset =
  let flgs = ref Flags.empty in
  (*
    - consume all epsilon moves, no duplicates allowed in the result
    - notice that the final evolved beta comes out in reverse order (as desired)
  *)
  let rec evolve rb st eb hits = match rb with
    |[] -> (!flgs, eb, hits)
    |i :: t when IntSet.mem i st -> evolve t st eb hits (* already explored the left-most occurence, ignore *)
    |i :: t ->
      let st = IntSet.add i st in
      match Nfa.get_state nfa i with
        |End |Kill -> evolve t st (i :: eb) hits
        |Pass j -> evolve (j :: t) st eb hits
        |MakeB j -> evolve (j :: t) st eb hits
        |EvalB j -> evolve (j :: t) st eb hits
        |BeginCap (_, j) -> evolve (j :: t) st eb hits
        |EndCap (_, j) -> evolve (j :: t) st eb hits
        |Match _ -> evolve t st (i :: eb) hits
        |CheckPred (P_BOI, j) ->
          if Word.is_empty w then evolve (j :: t) st eb hits else evolve t st eb hits
        |CheckPred (P_BOL ulines, j) ->
          begin
            match Word.tail w with
              |None -> evolve (j :: t) st eb hits
              |Some ((u, v), _) when u <= '\n' && '\n' <= v -> evolve (j :: t) st eb hits
              |Some ((u, v), _) when ulines && u <= '\r' && '\r' <= v -> evolve (j :: t) st eb hits
              |_ -> evolve t st eb hits
          end
        |CheckPred (P_EOI, _) ->
          evolve t st (i :: eb) hits
        |CheckPred _  | CheckBackref _ ->
          flgs := Flags.set_interrupted !flgs;
          evolve t st eb hits
        |BranchAlt (j, k) -> evolve (j :: k :: t) st eb hits
        |BranchKln (gd, j, k) ->
          (* record kleene hits, along with the corresponding left-beta *)
          let hits = if IntSet.mem i kset then (i, (i :: eb)) :: hits else hits in
          (* ordering implied by the quantifier must be taken into account when evolving a beta *)
          if gd then
            evolve (j :: k :: t) st eb hits
          else
            evolve (k :: j :: t) st eb hits in
  (* must reverse beta in order to be able to pattern match *)
  evolve (List.rev b) IntSet.empty [] [];;
