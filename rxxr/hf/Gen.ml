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
  a custom interval tree for grouping stuff by character ranges.
*)
type 'a itree = ITNull | ITNode of (char * char * 'a list * 'a itree ref * 'a itree ref);;

(*
  group (insert) stuff into an itree
*)
let rec insert_itree itr (u', v') lst' = match itr with
  ITNull ->
    ITNode (u', v', lst', ref ITNull, ref ITNull)|
  ITNode (u, _, _, lt, _) when v' < u ->
    let _ = lt := insert_itree !lt (u', v') lst' in
    itr|
  ITNode (_, v, _, _, rt) when u' > v ->
    let _ = rt := insert_itree !rt (u', v') lst' in
    itr|
  ITNode (u, v, lst, lt, rt) ->
    let _ = if u <> u' then
      let llst = if u' < u then lst' else lst in
      let luv = (min u u', ?-- (max u u')) in
      lt := insert_itree !lt luv llst in
    let _ = if v <> v' then
      let rlst = if v' > v then lst' else lst in
      let ruv = (?++ (min v v'), max v v') in
      rt := insert_itree !rt ruv rlst in
    ITNode (max u u', min v v', lst @ lst', lt, rt);;

(*
  collect all the kleene nodes (reachable or not) within a given regex
*)
let find_all_kleene r =
  let rt = Hashtbl.create 100 in
  let rec find_kleene' r' acc =
    let idx = (meta r')#id in
    match r' with
      _ when [] <> Hashtbl.find_all rt idx ->
        acc|
      Kleene (_, _, p, k) ->
        let _ = Hashtbl.add rt idx r' in
        find_kleene' !k (find_kleene' !p (r' :: acc))|
      Alt (_, pl, pr) ->
        let _ = Hashtbl.add rt idx r' in
        find_kleene' !pr (find_kleene' !pl acc)|
      Atom (_, _, k) ->
        let _ = Hashtbl.add rt idx r' in
        find_kleene' !k acc|
      Anchor (_, _, k) ->
        let _ = Hashtbl.add rt idx r' in
        find_kleene' !k acc|
      Empty (_, k) ->
        let _ = Hashtbl.add rt idx r' in
        find_kleene' !k acc|
      End ->
        acc in
  find_kleene' r [];;

(*
  collect all the reachable kleene nodes while generating prefixes for each of them

  NOTE: Anchors make it difficult to generate prefixes leading to kleene nodes, they do not
  consume characters and therefore we cannot generate characters to satisfy them, instead
  the strings generated for the surrounding regexes should be such that they satisfy the
  anchor.
*)
let find_reachable_kleene r =
  let rt = Hashtbl.create 100 in
  let rec find_kleene' r' pref pred acc =
    if [] <> Hashtbl.find_all rt ((meta r')#id, pred) then
      acc
    else (
      let _ = Hashtbl.add rt ((meta r')#id, pred) r' in
      match (pred, r') with
        (None, Kleene (_, _, p, k)) ->
          find_kleene' !k pref pred (find_kleene' !p pref pred ((r', List.rev pref) :: acc))|
        (Some _, Kleene (_, _, p, k)) ->
          (* This kleene star is not yet reachable, the predicate needs to be satisfied by the child node *)
          find_kleene' !k pref pred (find_kleene' !p pref pred acc)|
        (None, Alt (_, pl, pr)) ->
          find_kleene' !pr pref pred (find_kleene' !pl pref pred acc)|
        (Some _, Alt (_, pl, pr)) ->
          find_kleene' !pr pref pred (find_kleene' !pl pref pred acc)|
        (None, Atom (_, atm, k)) ->
          find_kleene' !k (atm :: pref) pred acc|
        (Some atmp, Atom (_, atm, k)) -> begin
          (*
            In order to go beyond this node, this atom should be capable of matching the predicate atom.
            We need to generate an atom which comes from the intersection of the two (if there's such).
          *)
          match Util.intersect_atom atm atmp with
            Some atm' ->
              find_kleene' !k (atm' :: pref) None acc|
            None ->
              acc
        end|
        (None, Empty (_, k)) ->
          find_kleene' !k pref pred acc|
        (Some _, Empty (_, k)) ->
          find_kleene' !k pref pred acc|
        (Some _, Anchor _) ->
          (*
            TODO: This could potentially make some kleene stars un-reachable. Ex. \b$, $\b, \b^ etc.
          *)
          acc|
        (None, Anchor (_, b, k)) -> begin
          match (b, pref) with
            (BInput, []) ->
              find_kleene' !k pref pred acc|
            (BLine, []) ->
              find_kleene' !k pref pred acc|
            (BLine, atm :: t) when Util.is_matching_char atm '\n' ->
              find_kleene' !k (Char '\n' :: t) pred acc|
            (ELine, _) ->
              find_kleene' !k pref (Some (Char '\n')) acc|
            (Wordb, []) ->
              find_kleene' !k pref (Some (Class cls_word)) acc|
            (Wordb, atm :: pref') ->
              let c_w = Util.intersect_atom atm (Class cls_word) in
              let c_nw = Util.intersect_atom atm (Class cls_nword) in
              begin
                match (c_w, c_nw) with
                  (None, Some atm') ->
                    find_kleene' !k (atm' :: pref') (Some (Class cls_word)) acc|
                  (Some atm', None) ->
                    find_kleene' !k (atm' :: pref') (Some (Class cls_nword)) acc|
                  _ ->
                    acc
              end|
            (NWordb, []) ->
              find_kleene' !k pref (Some (Class cls_nword)) acc|
            (NWordb, atm :: pref') ->
              let c_w = Util.intersect_atom atm (Class cls_word) in
              let c_nw = Util.intersect_atom atm (Class cls_nword) in
              begin
                match (c_w, c_nw) with
                  (None, Some atm') ->
                    find_kleene' !k (atm' :: pref') (Some (Class cls_nword)) acc|
                  (Some atm', None) ->
                    find_kleene' !k (atm' :: pref') (Some (Class cls_word)) acc|
                  _ ->
                    acc
              end|
            _ ->
              acc
        end|
        (_, End) ->
          acc
    ) in
  find_kleene' r [] None [];;

(*
  simulates a list of regexes of the form (regex, atom option). The second component
  represents a predicate (if present). Prefix (in reverse) is used to evaluate predicat
  nodes. This simulation derives the first character for each of the regexes on the list.
*)
let simulate lst pref =
  let redv = Hashtbl.create 100 in
  let rec simulate lst pref = match lst with
    [] ->
      []|
    (r, pred) :: t when [] <> Hashtbl.find_all redv ((meta r)#id, pred) ->
      (* node already visited in this step for this (r, predicate) pair, skip *)
      simulate t pref|
    (r, pred) :: t ->
      let _ = Hashtbl.add redv ((meta r)#id, pred) r in
      begin
        match (r, pred) with
          (Kleene (m, _, p, k), _) ->
            simulate ((!p, pred) :: (!k, pred) :: t) pref|
          (Alt (_, pl, pr), _) ->
            simulate ((!pl, pred) :: (!pr, pred) :: t) pref|
          (Atom (_, atm, k), None) ->
            (atm, !k) :: simulate t pref|
          (Atom (_, atm, k), Some atm') ->
            begin
              match Util.intersect_atom atm atm' with
                Some atm'' ->
                  (atm'', !k) :: simulate t pref|
                None ->
                  simulate t pref
            end|
          (Empty (_, k), _) ->
            simulate ((!k, pred) :: t) pref|
          (Anchor (_, b, k), _) ->
            (*
              TODO: pending predicates get ignored at anchor nodes. Assume that the pending anchor can be satisfied.
              This could derive some characters which are not actually accepted by the regex. For an example, \b\B
              will effectively act as the null-expression even though this piece of code let it pass-through. In
              the worst-case this might lead us to not being able to generate a suffix - but that's OK (this is a
              very rare case); we're good as long as we don't generate suffixes that doesn't work. In the future
              we have to revise the anchor support so that these cases can be handled in a clean way.
            *)
            begin
              match (b, pref) with
                (BInput, []) ->
                  simulate ((!k, None) :: t) pref|
                (ELine, _) ->
                  simulate ((!k, Some (Char '\n')) :: t) pref|
                (BLine, []) -> 
                  simulate ((!k, None) :: t) pref|
                (BLine, atm :: pref') when Util.is_matching_char atm '\n' ->
                  simulate [(!k, None)] (Char '\n' :: pref') @ simulate t pref|
                (Wordb, []) ->
                  simulate ((!k, Some (Class cls_word)) :: t) pref|
                (Wordb, atm :: pref') ->
                  let c_w = Util.intersect_atom atm (Class cls_word) in
                  let c_nw = Util.intersect_atom atm (Class cls_nword) in
                  begin
                    match (c_w, c_nw) with
                      (None, Some atm') ->
                        simulate [(!k, Some (Class cls_word))] (atm' :: pref') @ simulate t pref|
                      (Some atm', None) ->
                        simulate [(!k, Some (Class cls_nword))] (atm' :: pref') @ simulate t pref|
                      _ ->
                        simulate t pref
                  end|
                (NWordb, []) ->
                  simulate ((!k, Some (Class cls_nword)) :: t) pref|
                (NWordb, atm :: pref') ->
                  let c_w = Util.intersect_atom atm (Class cls_word) in
                  let c_nw = Util.intersect_atom atm (Class cls_nword) in
                  begin
                    match (c_w, c_nw) with
                      (None, Some atm') ->
                        simulate [(!k, Some (Class cls_nword))] (atm' :: pref') @ simulate t pref|
                      (Some atm', None) ->
                        simulate [(!k, Some (Class cls_word))] (atm' :: pref') @ simulate t pref|
                      _ ->
                        simulate t pref
                  end|
                _ ->
                  simulate t pref
            end|
          (End, _) ->
            simulate t pref
      end in
  simulate lst pref;;

(*
  check if the given node corresponds to an accepting state. For a node to be
  accepting, there should be an ε path from that node to the End node.
*)
let rec is_accepting r = match r with
  Kleene (_, _, _, k) ->
    is_accepting !k|
  Alt (_, lp, rp) ->
    (is_accepting !lp || is_accepting !rp)|
  Atom (_) ->
    false|
  Empty (_, k) ->
    is_accepting !k|
  Anchor (_, _, k) ->
    (* TODO: Here we make a rough approximation that there is some way to satisfy any anchor *)
    is_accepting !k|
  End ->
    true;;

(*
  check whether the continuation of the given regex has been bounded by an end-of-line or end-of-input anchor.
*)
let rec is_bounded r = match r with
  Kleene (_, _, _, k) ->
    is_bounded !k|
  Alt (_, lp, rp) ->
    (is_bounded !lp && is_bounded !rp)|
  Atom (_, _, k) ->
    is_bounded !k|
  Empty (_, k) ->
    is_bounded !k|
  Anchor (_, ELine, _) | Anchor (_, EInput, _) ->
    true|
  Anchor (_, _, k) ->
    is_bounded !k|
  _ ->
    false;;

(*
  explore the given lockstep machine and analyse the resulting sub-machines
  for a non-accepting configuration. The prefix of the machine should be in
  reverse order (required for easy evaluation of anchors).
*)
let explore (rpref, lst) =
  (* simulate the list of pointers *)
  let simmed = simulate lst rpref in
  (* sort the resulting regexes into an itree *)
  let itr = List.fold_left (
    fun itr (atm, r) -> match atm with
      Char c ->
        insert_itree itr (c, c) [(r, None)]|
      Class cls ->
        List.fold_left (fun itr rng -> insert_itree itr rng [(r, None)]) itr cls
  ) ITNull simmed in
  (* collect the resulting list of machines while calculating a possible non-matching next-atom *)
  let rec collect itr acc nmatch = match itr with
    ITNull ->
      (acc, nmatch)|
    ITNode (u, v, lst, lt, rt) when u = v ->
      let (acc, nmatch) = collect !lt acc (Util.subtract_range nmatch (u, v)) in
      collect !rt ((Char u :: rpref, lst) :: acc) nmatch|
    ITNode (u, v, lst, lt, rt) ->
      let (acc, nmatch) = collect !lt acc (Util.subtract_range nmatch (u, v)) in
      collect !rt ((Class [(u, v)]:: rpref, lst) :: acc) nmatch in
  let (machines, nmatch) = collect itr [] [('\x00', '\x7F')] in
  (* in case if we have an atom that cannot be matched by any of the sub-machines *)
  if nmatch <> [] then
    (Some (Class nmatch :: rpref), machines)
  else (
    (* scan the list of machines for a non-accepting configuration *)
    List.fold_left (
      fun (suffix, machines) (w, lst) ->
        if (List.fold_left (fun nomatch (r, _) -> if is_accepting r then false else nomatch) true lst) then
          (Some w, (w, lst) :: machines)
        else
          (suffix, (w, lst) :: machines)
    ) (None, []) machines
  );;

(*
  attempts to derive a string which fails to match the given (continuation) regex.
*)
let derive_nomatch r pref ubound = 
  let rpref = List.rev pref in
  let m = (rpref, [(r, None)]) in
  let rec step mlist scount = match (mlist, scount) with
    (_, 0) ->
      None|
    (h :: t, _) -> 
      begin
        match explore h with
          (None, next) ->
            step (t @ next) (scount - 1)|
          (Some w, _) ->
            let ldiff = List.length w - List.length rpref in
            let (_, suffix) = List.fold_left (
              fun (ldiff, suffix) atm ->
                if ldiff > 0 then (ldiff - 1, atm :: suffix) else (0, suffix)
            ) (ldiff, []) w in
            Some suffix
      end|
    _ ->
      None in
  (* r might not be an accepting state, so we can use the empty string as a suffix *)
  if is_accepting r then (
    if is_bounded r then
      step [m] ubound
    else
      (* if the continuation is not bounded, then any suffix will be matched by the implicit .* at the end - i.e a prefix match *)
      None
  ) else
    Some [];;
