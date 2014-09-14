(* © Copyright University of Birmingham, UK *)

open ParsingData

let zmin = '\x00';;
let zmax = '\x7f';;
let zprev u = if u <= zmin then zmin else Char.chr (Char.code u - 1);;
let znext u = if u >= zmax then zmax else Char.chr (Char.code u + 1);;

let chr_ignore_case c =
  let c_up = Char.uppercase c in
  let c_low = Char.lowercase c in
  if c_up != c then
    [(c_up, c_up); (c, c)]
  else if c_low != c then
    [(c, c); (c_low, c_low)]
  else
    [(c, c)];;

let cls_ignore_case cls =
  let (la, lz) = ('a', 'z') in
  let (ua, uz) = ('A', 'Z') in
  let rec ignore_case cls tr = match cls with
    [] -> ctr_positive tr
    |(u, v) :: t ->
      let tr = if max u la <= min v lz then ctr_add tr (Char.uppercase (max u la)) (Char.uppercase (min v lz)) else tr in
      let tr = if max u ua <= min v uz then ctr_add tr (Char.lowercase (max u ua)) (Char.lowercase (min v uz)) else tr in
      ignore_case t (ctr_add tr u v) in
  ignore_case cls CTNull;;

let zprint c = if c < '\x20' || c > '\x7e' then Printf.sprintf "\\x%02x" (Char.code c) else Printf.sprintf "%c" c;;
let cls_print cls =
  let rec cls_print2 acc cls = match cls with
    [] -> Printf.sprintf "[%s]" acc
    |(u, v) :: t when u == v -> let acc2 = Printf.sprintf "%s%s" acc (zprint u) in cls_print2 acc2 t
    |(u, v) :: t -> let acc2 = Printf.sprintf "%s%s-%s" acc (zprint u) (zprint v) in cls_print2 acc2 t in
  cls_print2 "" cls;;

module IntSet = Set.Make (struct type t = int let compare = Pervasives.compare end);;
module ProductSet = Set.Make (struct type t = int * int let compare = Pervasives.compare end);;
module IntListSet = Set.Make (struct type t = int list let compare = Pervasives.compare end);;
