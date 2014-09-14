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
  main matching routine
*)
val domatch : regex -> string -> (bool * int * string);;
