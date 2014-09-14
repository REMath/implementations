(************************************************************
 *                                                          *
 * RXXR - Regular eXpression eXponential Runtime analyser   *
 *                                                          *
 * Copyright (C) 2012 University of Birmingham              *
 *                                                          *
 * All rights reserved.                                     *
 *                                                          *
 * For license conditions, see the file LICENSE.rtf.        *
 *                                                          *
 ***********************************************************)

open Data;;
open Util;;

(*
  a customized range-tree type

  TODO: This is same as the itree structure used in the Gen module.
*)
type 'a rtree = Null | Node of char * char * 'a list * 'a rtree ref * 'a rtree ref;;

(*
  module for keeping track of (sorted) lists of derivatives (each derivative identified by the corresponding node id)
*)
module SortedListSet = Set.Make (
  struct
    let compare = Pervasives.compare
    type t = int list
  end)

(*
  used to signal an invalid state encountered during HF simulation
*)
exception HfError of string;;

(*
  formats the given list of derivatives into a string
*)
let dlist_to_string lst zid =
  let buf = Buffer.create 80 in
  let rec dlist_to_string' lst' = match lst' with
    (None, r, _) :: t when zid = (meta r)#id -> (
      Printf.bprintf buf "<_.(%d)>" zid;
      dlist_to_string' t)|
    (None, r, _) :: t -> (
      Printf.bprintf buf "<_.%d>" (meta r)#id;
      dlist_to_string' t)|
    (Some atm, r, _) :: t when zid = (meta r)#id -> (
      Printf.bprintf buf "<%s.(%d)>" (atom_to_string atm) zid;
      dlist_to_string' t)|
    (Some atm, r, _) :: t -> (
      Printf.bprintf buf "<%s.%d>" (atom_to_string atm) (meta r)#id;
      dlist_to_string' t)|
    [] ->
      Buffer.contents buf in
  dlist_to_string' lst;;

(*
  formats the given wdp machine into a string
*)
let wdp_to_string (w, dlist) zid =
  Printf.sprintf "%s.{%s}" (atoms_to_string w) (dlist_to_string dlist zid);;

(*
  formats a range-tree into a string
*)
let rec rtree_to_string tr = match tr with
  Null ->
    "Null"|
  Node (u, v, _, lt, rt) ->
    Printf.sprintf "{%s}.{%c, %c}.{%s}" (rtree_to_string !lt) u v (rtree_to_string !rt);;

(*
  insert stuff into a range-tree
*)
let rec insert_rtree t (u', v') dl' = match t with
  Null ->
    Node (u', v', dl', ref Null, ref Null)|
  Node (u, v, dl, tl, tr) when v' < u ->
    Node (u, v, dl, ref (insert_rtree !tl (u', v') dl'), tr)|
  Node (u, v, dl, tl, tr) when u' > v ->
    Node (u, v, dl, tl, ref (insert_rtree !tr (u', v') dl'))|
  Node (u, v, dl, tl, tr) ->
    let _ = if u <> u' then
      let ldl = if u < u' then dl else dl' in
      let luv = (min u u', ?-- (max u u')) in
      tl := insert_rtree !tl luv ldl in
    let _ = if v <> v' then
      let rdl = if v < v' then dl' else dl in
      let ruv = (?++ (min v v'), max v v') in
      tr := insert_rtree !tr ruv rdl in
    Node (max u u', min v v', dl' @ dl, tl, tr);;

(*
  simulates a list of derivatives until all of them get stuck.

  NOTE: This simulation must be an exhaustive search, we cannot perform
  any redundancy elimination as redundancies are what we're lookig for.
  A barrier stack (bs) is associated with each pointer which allows to
  avoid infinite recursion into kleene expressions which can match the
  empty string.
*)
let simulate dlist wlen zid =
  let rec simulate' lst = match lst with
    [] ->
      []|
    (_, End, _) :: _ | (Some _, _, _) :: _ ->
      raise (HfError "SIMULATE: Unexpected derivative")|
    (_, Anchor (_), _) :: _ ->
      raise (HfError "SIMULATE: Anchor support not implemented")|
    (_, Empty (_, k), bs) :: t ->
      simulate' ((None, !k, bs) :: t)|
    (_, Atom (_, atm, k), bs) :: t -> 
      (Some atm, !k, bs) :: simulate' t|
    (_, Alt (_, r1, r2), bs) :: t ->
      simulate' ((None, !r1, bs) :: (None, !r2, bs) :: t)|
    (_, Kleene (m, _, _, _), bs) as h :: t when zid = m#id ->
      begin
        match bs with
          [(x, y)] when x = zid ->
            if y < wlen then
              h :: simulate' t
            else
              simulate' t|
           _ ->
            raise (HfError "SIMULATE: Unexpected barrier stack")
      end|
    (_, Kleene (m, _, r, k), bs) :: t -> (* Gq / Rq quantifiers do not affect exponential vulnerabilities *)
      begin
        match bs with
          ((x, y) :: bs') when x = m#id ->
            if y < wlen  then
              simulate' ((None, !r, ((m#id, wlen) :: bs')) :: (None, !k, bs') :: t)
            else
              simulate' t|
          _ ->
            simulate' ((None, !r, ((m#id, wlen) :: bs)) :: (None, !k, bs) :: t)
      end in
  simulate' dlist;;

(*
  simulates the given list of derivatives and re-simulates if necessary
*)
let simulate_and_loop dlist wlen zid = 
  let sim_dlist = simulate dlist wlen zid in
  (* check for returning derivatives - i.e ones that have reached p0 *)
  let lpfilter pos = fun x -> match x with
    (None, r, _) when zid = (meta r)#id ->
      pos|
    _->
      not pos in
  (* if there's only one of them, we need to re-simulate it once more *)
  match List.filter (lpfilter true) sim_dlist with
    [(None, Kleene (_, _, p, _), _)] ->
      (simulate [(None, !p, [(zid, wlen)])] wlen zid) @ (List.filter (lpfilter false) sim_dlist)|
    _ ->
      sim_dlist;;

(*
  simulate the given machine and build the list of resultant machines
*)
let explore (w, dlist) zid = 
  let sim_dlist = simulate_and_loop dlist (List.length w) zid in
  let (dxs, t) = List.fold_left (fun (dxs, nd) dv ->
    match dv with
      (None, _, _) ->
        (dv :: dxs, nd)|
      (Some (Char c), r, bs) ->
        (dxs, insert_rtree nd (c, c) [(None, r, bs)])|
      (Some (Class rlist), r, bs) ->
        (dxs, List.fold_left (fun nd rng -> insert_rtree nd rng [(None, r, bs)]) nd rlist)
  ) ([], Null) sim_dlist in
  let rec collect tr mlist = match tr with
    Null ->
      mlist|
    Node (u, v, dl, lt, rt) when u = v ->
      collect !rt ((w @ [Char u], dl) :: collect !lt mlist)|
    Node (u, v, dl, lt, rt) ->
      collect !rt ((w @ [Class [(u, v)]], dl) :: collect !lt mlist) in
  let initms = if dxs <> [] then [(w, dxs)] else [] in
  collect t initms;;

(*
  counts the derivatives that has reached p0
*)
let rec count_zid dlist zid = 
  List.fold_left (
    fun count dv ->
      match dv with
        (None, r, _) when zid = (meta r)#id ->
          count + 1|
        _ ->
          count
  ) 0 dlist;;

(*
  partition function for quicksort on a list of derivatives
*)
let partition_dlist dlist (_, pvtr, _) =
  let rec partition_dlist lst less more = match lst with
    (_, r, _) as h :: t when (meta r)#id <= (meta pvtr)#id ->
      partition_dlist t (h :: less) more|
    h :: t ->
      partition_dlist t less (h :: more)|
    [] ->
      (less, more) in
  partition_dlist dlist [] [];;

(*
  quicksort procedure for a list of derivatives
*)
let rec quicksort_dlist dlist = match dlist with
  [] | [_] ->
    dlist|
  h :: t ->
    let (l, m) = partition_dlist t h in
    (quicksort_dlist l) @ (h :: quicksort_dlist m);;

(*
  advances the given wdp machine by one character while detecting possible pumpable strings
*)
let step m zid mset =
  let rec analyze mlist nextms mset = match mlist with
    [] ->
      (* no vulnerabilities detected, return the new list of machines *)
      ([], nextms, mset)|
    (w, lst) :: _ when (count_zid lst zid) > 1 ->
      (* vulnerability detected, cut short and report *)
      (w, [], mset)|
    (_, lst) as h :: t ->
      let sorted_dlist = quicksort_dlist lst in
      let sorted_id_list = List.fold_right (fun (_, r, _) acc -> (meta r)#id :: acc) sorted_dlist [] in
      if SortedListSet.mem sorted_id_list mset then
        (* machine already encountered earlier, no need to re-investigate *)
        analyze t nextms mset
      else
        (* unique sub-machine found, needs to be investigated *)
        analyze t (h :: nextms) (SortedListSet.add sorted_id_list mset) in
  analyze (explore m zid) [] mset;;
      
(*
  search for an exponential vulnerability in the given kleene expression
*)
let search_kleene r ubound = match r with
  Kleene (m, _, p, _) ->
    let stepc = ref 0 in
    let mset = SortedListSet.add [m#id] (SortedListSet.empty) in
    let rec search mlist mset = match mlist with
      [] ->
        ([], false)|
      h :: t ->
        if !stepc < ubound then
          let _ = stepc := !stepc + 1 in
          match step h m#id mset with
            ([], l, mset') ->
              search (t @ l) mset'|
            (w, _, _) ->
              (* if there's a vulnerability, the overflow flag should be ignored *)
              (w, false)
        else
          ([], true) in
    search [([], [(None, !p, [(m#id, 0)])])] mset|
  _ ->
    raise (HfError "SEARCH: Kleene expression expected");;
