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

(*
  symbol type of the alphabet - characters and character classes
*)
type atom = Char of char|
  Class of (char * char) list;; (* list of ranges *)

(*
  named character classes
*)
val cls_dot : (char * char) list;;
val cls_dotall : (char * char) list;;
val cls_digit : (char * char) list;;
val cls_ndigit : (char * char) list;;
val cls_space : (char * char) list;;
val cls_nspace : (char * char) list;;
val cls_word : (char * char) list;;
val cls_nword : (char * char) list;;

(*
  metadata for regexe nodes
*)
class mdata : int -> int -> int -> object method id : int method spos: int method epos : int end;; (* metadata *)

(*
  regex type definitions
*)
type regex = End| (* terminal continuation *)
  Empty of mdata * regex ref| (* epsilon expression *)
  Anchor of mdata * boundary * regex ref| (* anchor expressions *)
  Atom of mdata * atom * regex ref| (* character or character class *)
  Alt of mdata * regex ref * regex ref| (* alternation *)
  Kleene of mdata * qfier * regex ref * regex ref (* unbounded repetition *)
and qfier = Gq | Rq (* quantifiers *)
and boundary = BLine | ELine | Wordb | NWordb | BInput | EInput;; (* boundary identifiers *)

(*
  return the metadata object for the given regex
*)
val meta : regex -> mdata;;
