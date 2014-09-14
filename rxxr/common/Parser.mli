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
  used to flag syntax errors
*)
exception SyntaxError of string;;

(*
  used to flag parsing errors
*)
exception ParserError of string;;

(*
  function for parsing a regex string into a Thompson NFA
*)
val parse_thompson : string -> regex * regex ref list * int;;
