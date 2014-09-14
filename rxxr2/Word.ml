(* © Copyright University of Birmingham, UK *)

open Common

(* a list of character ranges - stored in reverse order *)
type t = (char * char) list;;

let empty = [];;

let is_empty w = match w with
  |[] -> true
  |_ -> false;;

let extend w cc = cc :: w;;

let append w1 w2 = w2 @ w1;;

let length w = List.length w;;

let tail w = match w with
  |[] -> None
  |(u, v) :: t -> Some ((u, v), t);;

let suffix w flen =
  let tlen = length w in
  let rec suffix w i = match (w, i) with
    |(w, i) when i == flen -> []
    |(h :: t, i) -> h :: suffix t (i - 1)
    |_ -> [] in
  if flen >= tlen then [] else suffix w tlen;;

(* calculate the intersection of two ranges *)
let intersect (u, v) (_u, _v) =
  if (v < _u || _v < u) then None else Some (max u _u, min v _v);;

(* select a printable character (if possible) from the specified range *)
let chr_select (u, v) =
  let rec chr_select (u, v) l = match l with
    |(_u, _v) :: t ->
      begin 
        match intersect (u, v) (_u, _v) with
          |None -> chr_select (u, v) t
          |Some (__u, __v) -> __u
      end
    |[] -> u in
  chr_select (u, v) [('a', 'z'); ('A', 'Z'); ('0', '9')];;

let select w = List.fold_left (fun l cc -> (chr_select cc) :: l) [] w;;

let print w = List.fold_left (fun s (u, v) -> Printf.sprintf "%s%s" (if u == v then zprint u else cls_print [(u, v)]) s) "" w;;
