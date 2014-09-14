(* © Copyright University of Birmingham, UK *)

open Nfa
open Common

(* collect all the kleene states within a given NFA *)
let find_kleene nfa =
  let rec explore i (st, lst) =
    if IntSet.mem i st then (st, lst) else
      let st = IntSet.add i st in
      match Nfa.get_state nfa i with
        |End | Kill -> (st, lst)
        |Pass j -> explore j (st, lst)
        |MakeB j -> explore j (st, lst)
        |EvalB j -> explore j (st, lst)
        |Match (_, j) -> explore j (st, lst)
        |CheckPred (_, j) -> explore j (st, lst) (* assume satisfiable - will be caught at later stages *)
        |CheckBackref (_, j) -> explore j (st, lst) (* assume satisfiable - will be caught at later stages *)
        |BeginCap (_, j) -> explore j (st, lst)
        |EndCap (_, j) -> explore j (st, lst)
        |BranchAlt (j, k) -> explore j (explore k (st, lst))
        |BranchKln (_, j, k) -> explore j (explore k (st, (i :: lst))) in
  snd (explore (Nfa.root nfa) (IntSet.empty, []));;

(* collect all the branch points within a given kleene expression *)
let find_branches nfa ik =
  let rec explore i (st, lst) =
    if IntSet.mem i st then (st, lst) else
      let st = IntSet.add i st in
      match Nfa.get_state nfa i with
        |End | Kill -> (st, lst)
        |Pass j -> explore j (st, lst)
        |MakeB j -> explore j (st, lst)
        |EvalB j -> explore j (st, lst)
        |Match (_, j) -> explore j (st, lst)
        |CheckPred (_, j) -> explore j (st, lst) (* assume satisfiable - will be caught at later stages *)
        |CheckBackref (_, j) -> explore j (st, lst) (* assume satisfiable - will be caught at later stages *)
        |BeginCap (_, j) -> explore j (st, lst)
        |EndCap (_, j) -> explore j (st, lst)
        |BranchAlt (j, k) -> explore j (explore k (st, (i, (j, k)) :: lst))
        |BranchKln (_, j, k) -> explore j (explore k (st, (i, (j, k)) :: lst)) in
  match Nfa.get_state nfa ik with
    |BranchKln (_, j, _) ->
      (* all the sub-expression wire back to ik, so we will never explore outside the kleene expression *)
      snd (explore j ((IntSet.singleton ik), []))
    |_ -> [];;

let is_epsilon_reachable nfa w src dst =
  let rec explore i st = match i with
    |i when i == dst -> true
    |i when IntSet.mem i st -> false
    |_ ->
      let st = IntSet.add i st in
      match Nfa.get_state nfa i with
        End | Kill | Match _ -> false
        |Pass j -> explore j st
        |MakeB j -> explore j st
        |EvalB j -> explore j st
        |CheckPred (P_BOI, j) -> if Word.is_empty w then explore j st else false
        |CheckPred (P_BOL ulines, j) ->
          begin
            match Word.tail w with
              |None -> explore j st
              |Some ((u, v),  _) when u <= '\n' && '\n' <= v -> explore j st
              |Some ((u, v),  _) when ulines && u <= '\r' && '\r' <= v -> explore j st
              |_ -> false
          end
        |CheckPred _ -> false (* not supported *)
        |CheckBackref _ -> false (* not supported *)
        |BeginCap (_, j) -> explore j st
        |EndCap (_, j) -> explore j st
        |BranchAlt (j, k) -> explore j st || explore k st
        |BranchKln (_, j, k) -> explore j st || explore k st in
  explore src IntSet.empty;;

(* a sorted tree of state vector pairs *)
type xtree = XTNull | XTNode of char * char * int list * int list * xtree * xtree;;

(* insert a new node into the tree - some nodes may have to be sliced in order to handle overlapping ranges *)
let rec xtr_add tr _u _v _l1 _l2 = match tr with
  XTNull -> XTNode (_u, _v, _l1, _l2, XTNull, XTNull)
  |XTNode (u, v, l1, l2, ltr, rtr) when _v < u -> XTNode (u, v, l1, l2, (xtr_add ltr _u _v _l1 _l2), rtr)
  |XTNode (u, v, l1, l2, ltr, rtr) when v < _u -> XTNode (u, v, l1, l2, ltr, (xtr_add rtr _u _v _l1 _l2))
  |XTNode (u, v, l1, l2, ltr, rtr) ->
    let _ltr = if u = _u then ltr else if u < _u then xtr_add ltr u (zprev _u) l1 l2 else xtr_add ltr _u (zprev u) _l1 _l2 in
    let _rtr = if v = _v then rtr else if _v < v then xtr_add rtr (znext _v) v l1 l2 else xtr_add rtr (znext v) _v _l1 _l2 in
    XTNode (max u _u, min v _v, _l1 @ l1, _l2 @ l2, _ltr, _rtr);;

(* compute all possible parallel transitions *)
let xtr_collect tr =
  let t_tbl = Hashtbl.create 8 in
  let rec explore tr = match tr with
    XTNull -> ()
    |XTNode (u, v, l1, l2, ltr, rtr) ->
      (* here we compute the cartesian product of the two state vectors, but we discard the ordering *)
      explore ltr; explore rtr; List.fold_left (fun _ i -> List.fold_left (fun _ j -> Hashtbl.add t_tbl (min i j, max i j) (u, v)) () l2) () l1 in
  explore tr; t_tbl;;

(* find all parallel transitions for the specified state pair *)
let get_parallel_transitions nfa ik (i1, i2) =
  let i1_lst = Nfa.get_transitions nfa i1 in
  let i2_lst = Nfa.get_transitions nfa i2 in
  (* we're only interested in transitions within the current kleene expression *)
  let tr = List.fold_left (fun tr (u, v, j) -> if j <= ik then xtr_add tr u v [j] [] else tr) XTNull i1_lst in
  let tr = List.fold_left (fun tr (u, v, j) -> if j <= ik then xtr_add tr u v [] [j] else tr) tr i2_lst in
  xtr_collect tr;;

let find_pumpable_kleene nfa =
  let result = Hashtbl.create 8 in
  (* collect converging products and eliminate redundancies *)
  let rec filter_convergences plist pcache nlist clist = match plist with
    [] -> (pcache, nlist, clist)
    |p :: t when (fst p) == (snd p) -> filter_convergences t pcache nlist (p :: clist)
    |p :: t ->
      if ProductSet.mem p pcache then
        (* product already encountered, ignore *)
        filter_convergences t pcache nlist clist
      else
        (* new product, needs to be simulated further *)
        filter_convergences t (ProductSet.add p pcache) (p :: nlist) clist in
  (* simulates a list of products until they either converge or disappear *)
  let rec check_convergence ik plist pcache = match plist with
    [] -> false
    |p :: t ->
      (* calculate the new list of products reachable from the current product *)
      let nprods = Hashtbl.fold (fun p2 _ lst -> p2 :: lst) (get_parallel_transitions nfa ik p) [] in
      (* check to see if there are any converging products *)
      match (filter_convergences nprods pcache t []) with
        (* no converging products, re-simulate the new list of products *)
        (pcache, nlist, []) -> check_convergence ik nlist pcache
        (* at least one product converged - we're done *)
        |_ -> true in
  (* filter out innner branches with parallel paths leading to a common state *)
  let rec filter_converging_branches ik blist = match blist with
    [] -> []
    |(i, p) :: t -> let tf = filter_converging_branches ik t in if (check_convergence ik [p] ProductSet.empty) then i :: tf else tf in
  (* analyse each kleene for pumpability *)
  let rec explore klns = match klns with
    [] -> ()
    |ik :: t ->
      (* collect pumpable kleene states along with the corresponding branch points *)
      let br_set = List.fold_left (fun s i -> IntSet.add i s) IntSet.empty (filter_converging_branches ik (find_branches nfa ik)) in
      let _ = if not (IntSet.is_empty br_set) then Hashtbl.add result ik br_set else () in
      explore t in
  explore (find_kleene nfa); result;;
