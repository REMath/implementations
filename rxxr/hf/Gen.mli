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
  collect all the kleene nodes (reachable or not) within a given regex
*)
val find_all_kleene : regex -> regex list;;

(*
  collect all the reachable kleene nodes while generating prefixes for each of them
*)
val find_reachable_kleene: regex -> (regex * atom list) list;;

(*
  attempts to derive a string which fails to match the given (continuation) regex.
*)
val derive_nomatch : regex -> atom list -> int -> atom list option;;
