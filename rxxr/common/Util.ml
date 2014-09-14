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
  calculate the next / previous character in the alphabet (input should not be at either extreme)
*)
let (?++) c = Char.chr (Char.code c + 1);;
let (?--) c = Char.chr (Char.code c - 1);;

(*
  utility function for exploding a string. 
*)
let explode_string s =
  let rec explode_string' i l =
    if i < 0 then l else explode_string' (i - 1) (s.[i] :: l) in
      explode_string' (String.length s - 1) [];;

(*
  adopt a character class so that it becomes case insensitive
*)
let ignore_case cls =
  let (la, lz) = ('a', 'z') in
  let (ua, uz) = ('A', 'Z') in
  let rec ignore_case cls = match cls with
    (u, v) :: t ->
      let lower_ignored = 
        if max u la <= min v lz then
          (Char.uppercase (max u la), Char.uppercase (min v lz)) :: (u, v) :: ignore_case t
        else 
          (u, v) :: ignore_case t in
      if max u ua <= min v uz then
        (Char.lowercase (max u ua), Char.lowercase (min v uz)) :: lower_ignored
      else
        lower_ignored|
    [] ->
      [] in
  ignore_case cls;; 

(*
  corrects the ordering of character classes such that x <= y in (x, y)
*)
let rec order_class lst = match lst with
  [] ->
    []|
  (x, y) :: t ->
    (min x y, max x y) :: order_class t;;

(*
  sort the character class in ascending order
*)
let rec quicksort_class lst = match lst with
  [] | [_] ->
    lst|
  h :: t -> let (lless, lmore) = partition_list t h [] [] in
    (quicksort_class lless) @ (h :: quicksort_class lmore)
and partition_list lst pivot lless lmore  = match lst with
  [] ->
    (lless, lmore)|
  h :: t when h <= pivot ->
    partition_list t pivot (lless @ [h]) lmore|
  h :: t ->
    partition_list t pivot lless (lmore @ [h]);;

(*
  order individual pairs, ignore cases (if requested), sort the class and strip overlaps
*)
let normalize_class lst icase =
  let rec normalize_class' lst' = match lst' with
    [] ->
      []|
    [a] ->
      [a]|
    (u, v) :: (u', v') :: t when u' <= ?++ v ->
      normalize_class' ((u, max v v') :: t)|
    h :: t ->
      h :: normalize_class' t in
  normalize_class' (quicksort_class (if icase then ignore_case (order_class lst) else order_class lst));;

(*
  calculate the negation of a class (input must be normalized)
*)
let negate_class lst =
  let rec negate_class' lst' prev = match lst' with
    [] when prev = '\x7F' ->
      []|
    [] ->
      [(prev, '\x7F')]|
    ((x, y) :: t) when x = '\x00' ->
      negate_class' t (?++ y)|
    ((x, y) :: t) ->
      (prev, ?-- x) :: negate_class' t (?++ y) in
  negate_class' lst '\x00';;

(*
  check if a character belongs to the specified class or not
*)
let rec is_character_in_class c cls = match cls with
  ((u, v) :: t) ->
    if c >= u && c <= v then true else is_character_in_class c t|
  _ ->
    false;;

(*
  check if two classes are overlapping or not
*)
let rec is_overlapping cls1 cls2 = match (cls1, cls2) with
  ((u, v) :: t, (u', v') :: t') ->
    if v < u' then
      is_overlapping t cls2
    else if v' < u then
      is_overlapping cls1 t'
    else
      true|
  _ ->
    false;;

(*
  check whether an atom can match a given character
*)
let is_matching_char atm c = match atm with
  Char u ->
    u = c|
  Class cls ->
    is_character_in_class c cls;;

(*
  check whether an atom can match a given character class
*)
let is_matching_class atm cls = match atm with
  Char u ->
    is_character_in_class u cls|
  Class cls' ->
    is_overlapping cls cls';;

(*
  find the intersection of the given two atoms (if there's such)
*)
let intersect_atom atm1 atm2 = match (atm1, atm2) with
  (Char c, _) when is_matching_char atm2 c ->
    Some (Char c)|
  (_, Char d) when is_matching_char atm1 d ->
    Some (Char d)|
  (Class clsl, Class clsr) ->
    begin
      let rec intersect cls1 cls2 = match (cls1, cls2) with
        ((u, v) :: t1, (u', v') :: t2) when v < u' ->
          intersect t1 cls2|
        ((u, v) :: t1, (u', v') :: t2) when u > v' ->
          intersect cls1 t2|
        ((u, v) :: t1, (u', v') :: t2) ->
          let overlap = (max u u', min v v') in
          if v' < v then
            overlap :: intersect ((?++ v', v) :: t1) t2
          else (
            if v' = v then
              overlap :: intersect t1 t2
            else
              overlap :: intersect t1 ((?++ v, v') :: t2)
          )|
        _ ->
          [] in
      match intersect clsl clsr with
        [] ->
          None|
        cls ->
          Some (Class cls)
    end|
  _ ->
    None;;

(*
  subtract a character range from a character class (ignore if there's no overlapping)
*)
let rec subtract_range cls (u', v') = match cls with
  (u, v) :: t when v' < u ->
    cls|
  (u, v) :: t when u' > v ->
    (u, v) :: subtract_range t (u', v')|
  (u, v) :: t when u < u' ->
    (u, ?-- u') :: subtract_range ((u', v) :: t) (u', v')|
  (u, v) :: t ->
    if v < v' then
      subtract_range t (?++v, v')
    else
      if v > v' then (?++ v', v) :: t else t|
  _ ->
    cls;;

(*
  check whether the given character is a printable character (' ' < x < '~')
*)
let is_printable c = '\x20' <= c && c <= '\x7E';;

(*
  format an atom into a string
*)
let atom_to_string atm = match atm with
  (Char x) ->
    if is_printable x then Printf.sprintf "%c" x else Printf.sprintf "\\x%02X" (Char.code x)|
  (Class l) ->
    let buf = Buffer.create 16 in
    let rec range_to_string lst = match lst with
      [] ->
        Printf.sprintf "[%s]" (Buffer.contents buf)|
      ((c, d) :: t) when c == d -> (
        if is_printable c then Printf.bprintf buf "%c" c else Printf.bprintf buf "\\x%02X" (Char.code c);
        range_to_string t)|
      ((c, d) :: t) -> (
        if is_printable c then Printf.bprintf buf "%c-" c else Printf.bprintf buf "\\x%02X-" (Char.code c);
        if is_printable d then Printf.bprintf buf "%c" d else Printf.bprintf buf "\\x%02X" (Char.code d);
        range_to_string t) in
    range_to_string l;;

(*
  convert an atom to a character, pick a printable character if one is available.
*)
let atom_to_char atm = match atm with
  Char x ->
    x|
  Class cls -> match intersect_atom atm (Class [('\x20', '\x7E')]) with
    Some (Char x) ->
      x|
    Some (Class ((_, v) :: _)) ->
      v|
    _ -> match cls with
      (_, v) :: t ->
        v|
      _ ->
        (* this should never happen *)
        '\x00';;

(*
  convert a list of atoms into a string, pick as many printable characters as possible.
*)
let atoms_to_nice atms = List.fold_left (
    fun s atm ->
      let c = atom_to_char atm in
      if is_printable c then Printf.sprintf "%s%c" s c else Printf.sprintf "%s\\x%02X" s (Char.code c)
  ) "" atms;;

(*
  formats a sequence of atoms into a string
*)
let atoms_to_string lst =
  let buf = Buffer.create 16 in
  let rec atoms_to_string' lst' = match lst' with
    [] ->
      Buffer.contents buf|
    (atm :: t) -> (
      Printf.bprintf buf "%s" (atom_to_string atm);
      atoms_to_string' t) in
  atoms_to_string' lst;;

(*
  formats a bondary market into a string
*)
let boundary_to_string b = match b with
  BLine ->
    "^"|
  ELine ->
    "$"|
  Wordb ->
    "\\b"|
  NWordb ->
    "\\B"|
  BInput ->
    "\\A"|
  EInput ->
    "\\z";;

(*
  utility method for printing a Thompson NFA
*)
let print_thompson r sz =
  let rvector = Array.create sz true in
  let rec print_thompson' r = 
    let i = (meta r)#id in
    match r with
      Empty (_, k) when rvector.(i) -> (
        rvector.(i) <- false;
        Printf.printf "%d: (), k = %d\n" i (meta !k)#id;
        print_thompson' !k)|
      Anchor (_, b, k) when rvector.(i) -> (
        rvector.(i) <- false;
        Printf.printf "%d: %s, k = %d\n" i (boundary_to_string b) (meta !k)#id;
        print_thompson' !k)|
      Atom (_, atm, k) when rvector.(i) -> (
        rvector.(i) <- false;
        Printf.printf "%d: %s, k = %d\n" i (atom_to_string atm) (meta !k)#id;
        print_thompson' !k)|
      Alt (_, pl, pr) when rvector.(i) -> (
        rvector.(i) <- false;
        Printf.printf "%d: (%d|%d)\n" i (meta !pl)#id (meta !pr)#id;
        print_thompson' !pl;
        print_thompson' !pr)|
      Kleene (_, qf, p, k) when rvector.(i) -> (
        rvector.(i) <- false;
        Printf.printf "%d: (%d)*%s, k = %d\n" i (meta !p)#id (if qf = Rq then "?" else "")  (meta !k)#id;
        print_thompson' !p;
        print_thompson' !k)|
      _->
       () in
  print_thompson' r;;
