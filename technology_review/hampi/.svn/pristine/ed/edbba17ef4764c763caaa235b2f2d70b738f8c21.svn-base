open Zchaff;;

module StringSet = Set.Make(String) ;;
module StringMap = Map.Make(String) ;;

module StringIntPair = 
struct
  type t = string * int

  let compare = compare
end ;;

module StringIntSet = Set.Make(StringIntPair) ;;

module StringStringPair = 
struct
  type t = string * string

  let compare = compare
end ;;

module StringStringSet = Set.Make(StringStringPair) ;;

type constraints = int array list

let rec iter_with_tail f = 
  function [] -> ()
         | (x::xs) -> f x xs; iter_with_tail f xs


let ordered_pairs l = 
  let ps = ref [] in
  iter_with_tail (fun x -> fun xs -> ps := !ps @ (List.map (fun y -> (x,y)) xs)) l;
  !ps

let zchaff = zchaff_InitManager ()
let _ = zchaff_SetNumVariables zchaff 0

let verbosity = ref 1
let input_file = ref ""
let step_width = ref 1
let start = ref 1
let continuous = ref false
let writeOutput = ref false
let outputFile = ref ""

let message_ch = ref stdout

let message u s = if !verbosity >= u then (output_string !message_ch (s ()); flush !message_ch)

let rec range start finish =
  if start > finish then [] else start :: (range (start+1) finish)

let rec repeat x = function 0 -> []
                          | n -> x :: (repeat x (n-1)) 

let rec remove_dups = function [] -> []
                             | (x::xs) -> x::(remove_dups (List.filter (fun y -> y<>x) xs))

let listindex x =
  let rec lindex a = 
    function [] -> raise Not_found
           | (y::ys) -> if x=y then a else lindex (a+1) ys 
  in
  lindex 0 
