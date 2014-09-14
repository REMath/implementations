(* © Copyright University of Birmingham, UK *)

open Common
open Nfa

(* a phi is represented by a set of integers *)
type t = IntSet.t;;

module PhiSet = Set.Make (
  struct
    type t = IntSet.t;;
    let compare = IntSet.compare;;
  end);;

let make ist = ist;;

let elems p = p;;

let compare p1 p2 = IntSet.compare p1 p2;;

let subset p1 p2 = IntSet.subset p1 p2;;

let print p = IntSet.fold (fun i s -> Printf.sprintf "%s%d," s i) p "";;

(* a sorted tree of phis *)
type itree = ITNull | ITNode of char * char * IntSet.t * itree * itree;;

(* insert new phi, overlapping ranges create bigger (union) phis *)
let rec itr_add tr _u _v _s = match tr with
  |ITNull -> ITNode (_u, _v, _s, ITNull, ITNull)
  |ITNode (u, v, s, ltr, rtr) when _v < u -> ITNode (u, v, s, itr_add ltr _u _v _s, rtr)
  |ITNode (u, v, s, ltr, rtr) when v < _u -> ITNode (u, v, s, ltr, itr_add rtr _u _v _s)
  |ITNode (u, v, s, ltr, rtr) ->
    let _ltr = if u == _u then ltr else if u < _u then itr_add ltr u (zprev _u) s else itr_add ltr _u (zprev u) _s in
    let _rtr = if v == _v then rtr else if _v < v then itr_add rtr (znext _v) v s else itr_add rtr (znext v) _v _s in
    ITNode (max u _u, min v _v, IntSet.union _s s, _ltr, _rtr);;

(* collect all the phis in the tree, along with the corresponding prefixes *)
let rec itr_collect tr w lst = match tr with
  |ITNull -> lst
  |ITNode (u, v, s, ltr, rtr) ->
    itr_collect rtr w (itr_collect ltr w ((Word.extend w (u, v), s) :: lst));;

(* find characters which yield no phis - useful when we want to fail the current phi *)
let itr_find_nomatch tr =
  let rec explore tr next lst = match tr with
    |ITNull -> (next, lst)
    |ITNode (u, v, _, ltr, rtr) ->
      let (next, lst) = explore rtr next lst in
      let (next, lst) = if v == (zprev next) then (u, lst) else (u, (znext v, zprev next) :: lst) in
      explore ltr next lst in
  let (next, lst) = explore tr '\x80' [] in
  if '\x00' < next then ('\x00', zprev next) :: lst else lst;;

let advance (nfa, w, p) =
  (* each transition gets added to the phi tree individually, the tree groups the transitions to make phis *)
  let tr = IntSet.fold (fun i tr -> List.fold_left (fun tr (u, v, j) -> itr_add tr u v (IntSet.singleton j)) tr (Nfa.get_transitions nfa i)) p ITNull in
  itr_collect tr w [];;

(* same as above, but also compute the characters which can fail the current phi entirely *)
let explore (nfa, w, p) =
  let tr = IntSet.fold (fun i tr -> List.fold_left (fun tr (u, v, j) -> itr_add tr u v (IntSet.singleton j)) tr (Nfa.get_transitions nfa i)) p ITNull in
  (itr_collect tr w [], itr_find_nomatch tr);;

let evolve (nfa, w, p) iopt =
  let flgs = ref Flags.empty in
  let rec evolve pl st ep = match pl with
    |[] -> (!flgs, ep)
    |i :: t when IntSet.mem i st -> evolve t st ep (* already represented in ep, ignore *)
    |i :: t ->
      let st = IntSet.add i st in
      match Nfa.get_state nfa i with
        |End ->
          flgs := Flags.set_accepting !flgs; (* accepting state reached *)
          evolve t st (IntSet.add i ep)
        |Kill -> evolve t st ep
        |Pass j -> evolve (j :: t) st ep
        |MakeB j -> evolve (j :: t) st ep
        |EvalB j -> evolve (j :: t) st ep
        |BeginCap (_, j) -> evolve (j :: t ) st ep
        |EndCap (_, j) -> evolve (j :: t ) st ep
        |Match _ -> evolve t st (IntSet.add i ep) (* fully evolved *)
        |CheckPred (P_BOI, j) ->
          if Word.is_empty w then evolve (j :: t) st ep else evolve t st ep
        |CheckPred (P_BOL ulines, j) ->
          begin
            match Word.tail w with
              |None -> evolve (j :: t) st ep
              |Some ((u, v), _) when u <= '\n' && '\n' <= v -> evolve (j :: t) st ep
              |Some ((u, v), _) when ulines && u <= '\r' && '\r' <= v -> evolve (j :: t) st ep
              |_ -> evolve t st ep
          end
        |CheckPred (P_EOI, _) ->
          flgs := Flags.set_eoihit !flgs;
          evolve t st (IntSet.add i ep)
        |CheckPred _ |CheckBackref _ ->
          flgs := Flags.set_interrupted !flgs;
          evolve t st ep
        |BranchAlt (j, k) ->
          evolve (j :: k :: t) st ep
        |BranchKln (_, j, k) ->
          let _ = match iopt with
            |None -> ()
            |Some ik ->
              (* check if this is the kleene we're interested in *)
              flgs := if ik == i then Flags.set_klnhit !flgs else !flgs in
          evolve (j :: k :: t) st ep in
  (* convert phi to a list of integers so that we can pattern match *)
  evolve (IntSet.fold (fun i l -> i :: l) p []) IntSet.empty IntSet.empty;;

(* utility method for checking if the given character class includes the target character *)
let rec matches cls c = match cls with
  |(u, v) :: t when u <= c && c <= v -> true
  |_ :: t -> matches t c
  |[] -> false;;

(* simulate phi against the given character *)
let chr_simulate (nfa, w, p) c =
  let flgs = ref Flags.empty in
  let rec simulate l st rp = match l with
    (* return flags as well as the updated prefix *)
    |[] -> (!flgs, Word.extend w (c, c), rp)
    |i :: t when IntSet.mem i st -> simulate t st rp
    |i :: t ->
      let st = IntSet.add i st in
      match Nfa.get_state nfa i with
        |End |Kill -> simulate t st rp
        |Pass j -> simulate (j :: t) st rp
        |MakeB j -> simulate (j :: t) st rp
        |EvalB j -> simulate (j :: t) st rp
        |BeginCap (_, j) -> simulate (j :: t) st rp
        |EndCap (_, j) -> simulate (j :: t) st rp
        (* this is where the matching / failing happens *)
        |Match (cls, j) -> if matches cls c then simulate t st (IntSet.add j rp) else simulate t st rp
        |CheckPred (P_BOI, j) ->
          if Word.is_empty w then simulate (j :: t) st rp else simulate t st rp
        |CheckPred (P_BOL ulines, j) ->
          begin
            match Word.tail w with
              |None -> simulate (j :: t) st rp
              |Some ((u, v), _) when u <= '\n' && '\n' <= v -> simulate (j :: t) st rp
              |Some ((u, v), _) when ulines && u <= '\r' && '\r' <= v -> simulate (j :: t) st rp
              |_ -> simulate t st rp
          end
        |CheckPred (P_EOI, _) -> simulate t st rp
        |CheckPred _ |CheckBackref _ ->
          flgs := Flags.set_interrupted !flgs;
          simulate t st rp
        |BranchAlt (j, k) ->
          simulate (j :: k :: t) st rp
        |BranchKln (_, j, k) ->
          simulate (j :: k :: t) st rp in
  (* convert phi to a list of integers so that we can pattern match *)
  simulate (IntSet.fold (fun i l -> i :: l) p []) IntSet.empty IntSet.empty;;

let simulate (nfa, w, p) cl =
  (* simulate the phi character-by-character *)
  let (f, w, p) = List.fold_left (fun (f, w, p) c ->
    let (_f, _w, _p) = chr_simulate (nfa, w, p) c in
    (Flags.union f _f, _w, _p) 
  ) (Flags.empty, w, p) cl in
  (* evolve phi before returning result *)
  let (_f, ep) = evolve (nfa, w, p) None in
  (Flags.union f _f, w, ep);;
