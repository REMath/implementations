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
  used to indicate errors in the input string
*)
exception InputError of string;;

(*
  convert the given hexa-decimal character into the corresponding decimal value
*)
let ctohex c =
  if c >= '0' && c <= '9' then
    Char.code c - Char.code '0'
  else if c >= 'a' && c <= 'f' then
    10 + (Char.code c - Char.code 'a')
  else if c >= 'A' && c <= 'F' then
    10 + (Char.code c - Char.code 'A')
  else
    raise (InputError (Printf.sprintf "Invalid hexa-decimal character: %c" c));;

(*
  convert all hexa-decimal escapes to ascii characters
*)
let hescape s = 
  let buf = Buffer.create 64 in
  let slen = String.length s in
  let rec hescape s idx =
    if idx + 3 < slen && s.[idx] = '\\' && s.[idx + 1] = 'x' then (
      let hx = (ctohex s.[idx + 2] * 16) + (ctohex s.[idx + 3]) in
      if hx <= 127 then
        let _ = Buffer.add_char buf (Char.chr hx) in
        hescape s (idx + 4) 
      else
        raise (InputError (Printf.sprintf "Hexa-decimal escape out-of ascii range: \\x%X" hx))
    ) else (
      if idx < slen then
        let _ = Buffer.add_char buf s.[idx] in
        hescape s (idx + 1)
      else
        Buffer.contents buf
    ) in
  hescape s 0;;

(*
  main
*)
try
  let _ = Printf.printf "Input expression: " in
  let exp = read_line () in
  let _ = Printf.printf "Subject string: " in
  let s = read_line () in
  let (r, _, sz) = Parser.parse_thompson exp in
(*  Util.print_thompson r sz *)
  match Pwf.domatch r (hescape s) with
    (false, i, _) ->
      Printf.printf "No match.\nStep count: %d\n" i|
    (true, i, s') ->
      Printf.printf "Matched: %s\nStep count: %d\n" s' i
with
  InputError (msg) ->
    Printf.eprintf "Error: %s\n" msg|
  Lexer.LexicalError (msg) ->
    Printf.eprintf "Error: %s\n" msg|
  Parser.SyntaxError (msg) ->
    Printf.eprintf "Error: %s\n" msg;;
