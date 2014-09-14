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
  used to signal an invalid state encountered during HF simulation
*)
exception HfError of string;;

(*
  search for an exponential vulnerability in the given kleene expression
*)
val search_kleene : regex -> int -> (atom list * bool);;
