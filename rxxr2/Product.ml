(* © Copyright University of Birmingham, UK *)

open Common
open Nfa

(* an NFA state and a phi *)
type t = (int * Phi.t);;

module ProductSet = Set.Make (
  struct
    type t = (int * Phi.t);;
    let compare (i1, p1) (i2, p2) =
      let ic = Pervasives.compare i1 i2 in
      if ic == 0 then Phi.compare p1 p2 else ic;;
  end);;

let make i p = (i, p);;

let elems (i, p) = (i, p);;

(* a sorted tree of two parallel transitions *)
type ptree = PTNull | PTNode of char * char * IntSet.t * IntSet.t * ptree * ptree;;

(* inserts a new parallel transition, some nodes may get sliced due to overlapping character classes *)
let rec ptr_add tr _u _v _s1 _s2 = match tr with
  |PTNull -> PTNode (_u, _v, _s1, _s2, PTNull, PTNull)
  |PTNode (u, v, s1, s2, ltr, rtr) when _v < u -> PTNode (u, v, s1, s2, ptr_add ltr _u _v _s1 _s2, rtr)
  |PTNode (u, v, s1, s2, ltr, rtr) when v < _u -> PTNode (u, v, s1, s2, ltr, ptr_add rtr _u _v _s1 _s2)
  |PTNode (u, v, s1, s2, ltr, rtr) ->
    let _ltr = if u == _u then ltr else if u < _u then ptr_add ltr u (zprev _u) s1 s2 else ptr_add ltr _u (zprev u) _s1 _s2 in
    let _rtr = if v == _v then rtr else if _v < v then ptr_add rtr (znext _v) v s1 s2 else ptr_add rtr (znext v) _v _s1 _s2 in
    PTNode (max u _u, min v _v, IntSet.union s1 _s1, IntSet.union s2 _s2, _ltr, _rtr);;

(* collect all the parallel transitions *)
let rec ptr_collect tr w lst = match tr with
  |PTNull -> lst
  |PTNode (u, v, s1, s2, ltr, rtr) ->
    (* phi is the entire second set of states *)
    let p = Phi.make s2 in
    (* each state on the first set gives rise to a new product *)
    let lst = IntSet.fold (fun i l -> (Word.extend w (u, v), (i, p)) :: l) s1 lst in
    ptr_collect rtr w (ptr_collect ltr w lst);;

let advance (nfa, w, (i, p)) =
  (* begin with all the transitions of the first NFA state *)
  let tr = List.fold_left (
    fun tr (u, v, i) -> ptr_add tr u v (IntSet.singleton i) IntSet.empty
  ) PTNull (Nfa.get_transitions nfa i) in
  (* add all the reachable phis *)
  let tr = IntSet.fold (
    fun i tr -> List.fold_left (
      fun tr (u, v, i) -> ptr_add tr u v IntSet.empty (IntSet.singleton i)
    ) tr (Nfa.get_transitions nfa i)
  ) (Phi.elems p) tr in
  (* all the NFA transitions and the phis are now grouped in the tree *)
  ptr_collect tr w [];;

let evolve (nfa, w, (i, p)) brset =
  (* evolve the phi component *)
  let (flgs, ep) = Phi.evolve (nfa, w, p) None in
  let flgs = ref flgs in
  (* explore the NFA state looking for branch points *)
  let rec evolve pl st tpl = match pl with
    (* return the evolved product (the NFA component is left untouched) and the resulting triples *)
    |[] -> (!flgs, (i, ep), tpl) 
    |i :: t when IntSet.mem i st -> evolve t st tpl (* already explored, ignore *)
    |i :: t ->
      let st = IntSet.add i st in
      match Nfa.get_state nfa i with
        |End |Kill -> evolve t st tpl
        |Pass j -> evolve (j :: t) st tpl
        |MakeB j -> evolve (j :: t) st tpl
        |EvalB j -> evolve (j :: t) st tpl
        |BeginCap (_, j) -> evolve (j :: t) st tpl
        |EndCap (_, j) -> evolve (j :: t) st tpl
        |Match _ -> evolve t st tpl
        |CheckPred (P_BOI, j) ->
          if Word.is_empty w then evolve (j :: t) st tpl else evolve t st tpl
        |CheckPred (P_BOL ulines, j) ->
          begin
            match Word.tail w with
              |None -> evolve (j :: t) st tpl
              |Some ((u, v), _) when u <= '\n' && '\n' <= v -> evolve (j :: t) st tpl
              |Some ((u, v), _) when ulines && u <= '\r' && '\r' <= v -> evolve (j :: t) st tpl
              |_ -> evolve t st tpl
          end
        |CheckPred (P_EOI, _) ->
          evolve t st tpl
        |CheckPred _ | CheckBackref _ ->
          flgs := Flags.set_interrupted !flgs;
          evolve t st tpl
        |BranchAlt (j, k) when IntSet.mem i brset -> (* wanted branch point *)
          evolve (j :: k :: t) st (Triple.make j k ep :: tpl)
        |BranchAlt (j, k) ->
          evolve (j :: k :: t) st tpl
        |BranchKln (_, j, k) when IntSet.mem i brset -> (* wanted branch point *)
          evolve (j :: k :: t) st (Triple.make j k ep :: tpl)
        |BranchKln (_, j, k) ->
          evolve (j :: k :: t) st tpl in
  evolve [i] IntSet.empty [];;
