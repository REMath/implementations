(* © Copyright University of Birmingham, UK *)

(* internal representation of a word *)
type t;;

(* empty word - epsilon *)
val empty : t;;

(* check for empty word *)
val is_empty : t -> bool;;

(* append a character (or class) *)
val extend : t -> (char * char) -> t;;

(* append a word *)
val append : t -> t -> t;;

(* calculate the length of word *)
val length : t -> int;;

(* returns the final character (or class) and the rest of the word *)
val tail : t -> ((char * char) * t) option;;

(* returns the suffix which comes after the specified prefix *)
val suffix : t -> int -> t;;

(* select a candidate string (no classes) from the specified word *)
val select : t -> char list;;

(* print the word as it is *)
val print : t -> string;;
