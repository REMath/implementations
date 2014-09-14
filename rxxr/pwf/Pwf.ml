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

(*
  defines an PW frame (regex, barrier stack, w)
*)
type pw = regex * (int * int) list * int;;

(*
  check if the given position of the string is a word boundary (i represents the next character to be matched)
*)
let is_word_boundary s i =
  let slen = String.length s in
  if i = 0 && slen > 0 then
    Util.is_character_in_class s.[0] Data.cls_word
  else if i = slen && i > 0 then 
    Util.is_character_in_class s.[i - 1] Data.cls_word
  else if i > 0 && i < slen then
    if Util.is_character_in_class s.[i - 1] Data.cls_word then
      Util.is_character_in_class s.[i] Data.cls_nword
    else
      Util.is_character_in_class s.[i] Data.cls_word
  else
    false;;

(*
  main matching routine
*)
let domatch r s =
  let slen = String.length s in
  let steps = ref 0 in
  let (init_state : pw list) = [(r, [], 0)] in
  let rec simulate (lst : pw list) =
    let _ = steps := !steps + 1 in
      match lst with
      [] ->
        (false, !steps - 1, "")|
      (End, _, i) :: t ->
        (true, !steps - 1, String.sub s 0 i)|
      (Empty (_, k), bs, i) :: t ->
        simulate ((!k, bs, i) :: t)|
      (Anchor (_, BLine, k), bs, i) :: t when (i = 0 || s.[i - 1] = '\n') ->
        simulate ((!k, bs, i) :: t)|
      (Anchor (_, ELine, k), bs, i) :: t when (i = slen) || (i + 1 < slen && s.[i + 1] = '\n') ->
        simulate ((!k, bs, i) :: t)|
      (Anchor (_, Wordb, k), bs, i) :: t when is_word_boundary s i ->
        simulate ((!k, bs, i) :: t)|
      (Anchor (_, NWordb, k), bs, i) :: t when not (is_word_boundary s i) ->
        simulate ((!k, bs, i) :: t)|
      (Anchor (_, BInput, k), bs, i) :: t when i = 0 ->
        simulate ((!k, bs, i) :: t)|
      (Anchor (_, EInput, k), bs, i) :: t when i = slen ->
        simulate ((!k, bs, i) :: t)|
      (Anchor (_), bs, i) :: t ->
        simulate t|
      (Atom (_, atm, k), bs, i) :: t when (i < slen &&  Util.is_matching_char atm s.[i]) -> 
        simulate ((!k, bs, i + 1) :: t)|
      (Atom (_), _, _) :: t -> 
        simulate t|
      (Alt (_, r1, r2), bs, i) :: t ->
        simulate ((!r1, bs, i) :: (!r2, bs, i) :: t)|
      (Kleene (m, qf, r, k), bs, i) :: t -> begin
        match bs with
          ((x, y) :: bs') when x = m#id ->
            if y < i then
              if qf = Gq then
                simulate ((!r, ((m#id, i) :: bs'), i) :: (!k, bs', i) :: t)
              else
                simulate ((!k, bs', i) :: (!r, ((m#id, i) :: bs'), i) :: t)
            else
              simulate t|
          _ ->
            if qf = Gq then
              simulate ((!r, ((m#id, i) :: bs), i) :: (!k, bs, i) :: t)
            else
              simulate ((!k, bs, i) :: (!r, ((m#id, i) :: bs), i) :: t)
      end in
  simulate init_state;;
