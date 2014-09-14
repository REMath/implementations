(* © Copyright University of Birmingham, UK *)

(* first / last character of the alphabet - ASCII *)
val zmin : char;;
val zmax : char;;

(* calculate previous / next character in ASCII *)
val zprev : char -> char;;
val znext : char -> char;;

(* form case insensitive character class *)
val chr_ignore_case : char -> (char * char) list;;
val cls_ignore_case : (char * char) list -> (char * char) list;;

(* format characters / character classes for output *)
val zprint : char -> string;;
val cls_print : (char * char) list -> string;;

(* basic set definitions *)
module IntSet : (Set.S with type elt = int);;
module ProductSet : (Set.S with type elt = int * int);;
module IntListSet : (Set.S with type elt = int list);;
