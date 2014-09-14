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
  token type definitions 
*)
type token = 
  Literal of char|
  Class of (char * char) list|
  Anchor of boundary|
  Positive of int|
  VBar|
  Asterix|
  Plus|
  QMark|
  LSquare|
  CNegate|
  CRange|
  RSquare|
  LCurly|
  RCurly|
  LParen|
  RParen|
  EOS;;

(*
  used to flag lexical errors 
*)
exception LexicalError of string;;

(*
  record for keeping track of modifiers that matter to us.
*)
type modifiers = {dotall: bool ref; icase : bool ref; mline : bool ref};;

(*
  creates a tokenizer object
*)
val make_tokenizer : string -> (< next : token; peek : token; eat : token -> 'a; hpos : int; mods : modifiers; rest : string > as 'a);;
