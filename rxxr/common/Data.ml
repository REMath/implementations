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
let cls_dot = [('\x00', '\x09'); ('\x0B', '\x7F')];;
let cls_dotall = [('\x00', '\x7F')];;
let cls_digit = [('\x30', '\x39')];;
let cls_ndigit = [('\x00', '\x2F'); ('\x3A', '\x7F')];;
let cls_space = [('\x09', '\x0D'); ('\x20', '\x20')];;
let cls_nspace =  [('\x00', '\x08'); ('\x0E', '\x1F'); ('\x21', '\x7F')];;
let cls_word =  [('\x30', '\x39'); ('\x41', '\x5A'); ('\x5F', '\x5F'); ('\x61', '\x7A')];;
let cls_nword =  [('\x00', '\x2F'); ('\x3A', '\x40'); ('\x5B', '\x5E'); ('\x60', '\x60'); ('\x7B', '\x7F')];;

(*
  metadata for regexe nodes
*)
class mdata (id : int) (spos : int) (epos : int) =
  object
    method id = id
    method spos = spos
    method epos = epos
  end;;

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
  return the metadata for the given regex
*)
let meta r = match r with
  End ->
    new mdata (-1) 0 0|
  Empty (m, _) ->
    m|
  Anchor (m, _, _) ->
    m|
  Atom (m, _, _) ->
    m|
  Alt (m, _, _) ->
    m|
  Kleene (m, _, _, _) ->
    m;;
