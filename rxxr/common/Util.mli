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
val (?++) : char -> char;;
val (?--) : char -> char;;

(*
  utility function for exploding a string. 
*)
val explode_string : string -> char list;;

(*
  order individual pairs, ignore cases (if requested), sort the class and strip overlaps
*)
val normalize_class : (char * char) list -> bool -> (char * char) list;;

(*
  calculate the negation of a class (input must be normalized)
*)
val negate_class : (char * char) list -> (char * char) list;;

(*
  check if a character belongs to the specified class or not
*)
val is_character_in_class : char -> (char * char) list -> bool;;

(*
  check whether an atom can match a given character
*)
val is_matching_char : atom -> char -> bool;;

(*
  check whether an atom can match a given character class
*)
val is_matching_class : atom -> (char * char) list -> bool;;

(*
  find the intersection of the given two atoms (if there's such)
*)
val intersect_atom : atom -> atom -> atom option;;

(*
  subtract a character range from a character class (ignore if there's no overlapping)
*)
val subtract_range : (char * char) list -> (char * char) -> (char * char) list;;

(*
  formats an atom into a string
*)
val atom_to_string : atom -> string;;

(*
  formats a sequence of atoms into a string
*)
val atoms_to_string : atom list -> string;;

(*
  convert a list of atoms into a string, pick as many printable characters as possible.
*)
val atoms_to_nice : atom list -> string;;

(*
  formats a bondary market into a string
*)
val boundary_to_string : boundary -> string;;

(*
  utility method for printing a Thompson NFA
*)
val print_thompson : regex -> int -> unit;;
