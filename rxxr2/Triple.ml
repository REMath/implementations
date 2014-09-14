(* © Copyright University of Birmingham, UK *)

open Common

(* internal representation - an NFA state pair and a phi *)
type t = (int * int) * Phi.t;;

module TripleSet = Set.Make (
  struct
    type t = (int * int) * Phi.t;;
    let compare (i1, p1) (i2, p2) = let c = Pervasives.compare i1 i2 in if c == 0 then Phi.compare p1 p2 else c;; 
  end);;

let make i j p = ((i, j), p);;

let elems ((i, j), p) = (i, j, p);;

(* a sorted tree of three parallel transitions (corresponding to two NFAs and a phi) *)
type ttree = TTNull | TTNode of char * char * IntSet.t * IntSet.t * IntSet.t * ttree * ttree;;

(* insert a new triple, some nodes may get sliced due to overlapping character classes *)
let rec ttr_add tr _u _v _s1 _s2 _s3 = match tr with
  |TTNull -> TTNode (_u, _v, _s1, _s2, _s3, TTNull, TTNull)
  |TTNode (u, v, s1, s2, s3, ltr, rtr) when _v < u -> TTNode (u, v, s1, s2, s3, ttr_add ltr _u _v _s1 _s2 _s3, rtr)
  |TTNode (u, v, s1, s2, s3, ltr, rtr) when v < _u -> TTNode (u, v, s1, s2, s3, ltr, ttr_add rtr _u _v _s1 _s2 _s3)
  |TTNode (u, v, s1, s2, s3, ltr, rtr) ->
    let _ltr = if u == _u then ltr else if u < _u then ttr_add ltr u (zprev _u) s1 s2 s3 else ttr_add ltr _u (zprev u) _s1 _s2 _s3 in
    let _rtr = if v == _v then rtr else if _v < v then ttr_add rtr (znext _v) v s1 s2 s3 else ttr_add rtr (znext v) _v _s1 _s2 _s3 in
    TTNode (max u _u, min v _v, IntSet.union s1 _s1, IntSet.union s2 _s2, IntSet.union s3 _s3, _ltr, _rtr);;

(* compute all reachable triples *)
let rec ttr_collect tr w lst = match tr with
  |TTNull -> lst
  |TTNode (u, v, s1, s2, s3, ltr, rtr) ->
    (* phi is basically the entire third set *)
    let p = Phi.make s3 in
    (*
      - here we must calculate the cross product between the two sets corresponding to the parallel NFAs
      - ignores ordering (the order of the two NFAs does not matter for the analysis) 
    *)
    let lst = IntSet.fold (fun i l ->
      IntSet.fold (fun j l ->
        (Word.extend w (u, v), ((min i j, max i j), p)) :: l
      ) s2 l
    ) s1 lst in
    ttr_collect rtr w (ttr_collect ltr w lst);;

let advance (nfa, w, ((i, j), p)) =
  (* begin with all the transitions of the first NFA *)
  let tr = List.fold_left (
    fun tr (u, v, i) -> ttr_add tr u v (IntSet.singleton i) IntSet.empty IntSet.empty
  ) TTNull (Nfa.get_transitions nfa i) in
  (* combine with all the transitions of the second NFA *)
  let tr = List.fold_left (
    fun tr (u, v, i) -> ttr_add tr u v IntSet.empty (IntSet.singleton i) IntSet.empty
  ) tr (Nfa.get_transitions nfa j) in
  (* finally add all the transitions of the phi *)
  let tr = IntSet.fold (
    fun i tr -> List.fold_left (
      fun tr (u, v, i) -> ttr_add tr u v IntSet.empty IntSet.empty (IntSet.singleton i)
    ) tr (Nfa.get_transitions nfa i)
  ) (Phi.elems p) tr in
  (* all the transitions are now grouped in the tree, compute triples *)
  (ttr_collect tr w []);;

(*
  Sorting the triples before returning sometimes lead to faster results, especially with very large
  Kleene expressions. Basically, we need to make sure that triples are converged into the Kleene node
  as soon as possible (otherwise they can wander about inside a large Kleene expression for quite some
  time). This aspect need to be re-visited and expanded later on; it sounds like finding the shortest
  path from a given triple to the target Kleene node. 

  List.sort (fun (_, (ij1, _)) (_, (ij2, _)) -> Pervasives.compare ij1 ij2) (ttr_collect tr w []);;
*) 
