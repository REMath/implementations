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
open Util;;

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
  list of characters that is OK to be quoted with a backslash
*)
let escapables = ['|'; '*'; '+'; '?'; '{'; '}'; '['; ']'; '^'; '-'; '.'; '('; ')'; '\\'; ','; '$'; '\''; ':'; '/'; '@'; '<'; '>'; ' '; '&'; '='; '"'; '%'; ';'; '#'; '_'; '!'; '~'];;

(*
  list of global modifiers that we recognize. Note that we have deliberately excluded
  the following modifiers so that they can be taken care of manually (for the moment):

  x - White spaces (pre-process manually)
  e, X, J, u - Unsupported (PCRE / Perl)

  The following Snort-specific modifiers are ignored. These directives do not affect the
  semantics of the regex, rather, they are special directives for Snort indicating how
  a particular regex is to be utilized: http://manual.snort.org/node393.html

  R, U, I, P, H, D, M, C, K, S, Y, B, O
*)
let modifier_directives = ['i'; 'm'; 's'; 'g'; 'c'; 'A'; 'E'; 'G'; 'D'; 'R'; 'U'; 'I'; 'P'; 'H'; 'D'; 'M'; 'C'; 'K'; 'S'; 'Y'; 'B'; 'O'];;

(*
  record for keeping track of modifiers that matter to us.

  NOTE: Ideally the modifiers should be kept along with the regex.
  However, most of these modifiers don't affect the vulnerability
  status of a regex, and we don't support in-line modifiers at the
  moment. So it is sufficient to strip off the does-not-matter ones
  and make necessary adjustments in the lexer. In the future we need
  to revamp the regex structure and add full support for modifiers.
*)
type modifiers = {dotall: bool ref; icase : bool ref; mline : bool ref};; 

(*
  formats a token into a string 
*)
let format_token tk = match tk with
  EOS-> ""|
  VBar -> "|"|
  Asterix -> "*"|
  Plus -> "+"|
  QMark -> "?"|
  Anchor (b) -> Util.boundary_to_string b| 
  LSquare -> "["|
  CNegate -> "^"|
  CRange -> "-"|
  RSquare -> "]"|
  Class rlist -> Util.atom_to_string (Data.Class rlist)|
  LCurly -> "{"|
  RCurly -> "}"|
  Positive i -> Printf.sprintf "%d" i|
  LParen -> "("|
  RParen -> ")"|
  Literal c -> Printf.sprintf "%c" c;;

(*
  parse global modifiers and calculate the indices corresponding to
  the main regex.

  NOTE: The regex is assumed to be of the form /REGEX/MODIFIERS or
  just REGEX (i.e the whole string as the regex). In the future we
  might want to add support for other possible formations.
*)
let extract_modifiers exp =
  let exp_len = String.length exp in
  let mods = {dotall = ref false; icase = ref false; mline = ref false} in
  if exp_len = 0 || exp.[0] <> '/' then
    (mods, (0, exp_len - 1))
  else (
    let ridx = String.rindex exp '/' in
    if ridx <> 0 then
      (* walk through the modifier indicators *)
      let rec parse_modifiers idx =
        if idx < exp_len then
          match exp.[idx] with
            c when not (List.exists (fun x -> c = x) modifier_directives) ->          
              raise (LexicalError (Printf.sprintf "Unknown global modifier: %c" c))|
            's' ->
              let _ = mods.dotall := true in
              parse_modifiers (idx + 1)|
            'i' ->
              let _ = mods.icase := true in
              parse_modifiers (idx + 1)|
            'm' ->
              let _ = mods.mline := true in
              parse_modifiers (idx + 1)|
            _ ->
              parse_modifiers (idx + 1)
        else
          mods in
      (parse_modifiers (ridx + 1), (1, ridx - 1))
    else
      (mods, (0, exp_len - 1))
  );;

(*
  creates a character reader object
*)
let make_chreader exp (i, j) =
  let hpos = ref i in
  object (me)
    method next = 
      if !hpos <= j then
        let _ = hpos := !hpos + 1 in
        exp.[!hpos - 1]
      else
        '\x00'
    method peek =
      if !hpos <= j then
        exp.[!hpos]
      else
        '\x00'
    method eat c = 
      if !hpos <= j && c = exp.[!hpos] then
        let _ = hpos := !hpos + 1 in
        me
      else
        raise (LexicalError (Printf.sprintf "Expected character [%c] at column: %d" c !hpos))
    method hpos = 
      !hpos
    method rest = 
      if !hpos <= j then String.sub exp !hpos (j - !hpos + 1) else ""
  end;;

(*
  parse a single positive integer in decimal notation
*)
let parse_positive_decimal rdr = match rdr#peek with
  c when c >= '0' && c <= '9' ->
    let rec parse_positive_decimal' acc = match rdr#peek with
      d when d >= '0' && d <= '9' ->
        let _ = rdr#next in
        parse_positive_decimal' (10 * acc + (Char.code d - Char.code '0'))|
      _->
        acc in
    parse_positive_decimal' 0|
  _ ->
    raise (LexicalError "Expected decimal digit");;

(*
  parse an ascii character expressed as an octal value (\0n | \0nn | \0nnn)
*)
let parse_octal_ascii rdr = match rdr#peek with
  c when (c >= '0' && c <= '7') ->
    let rec parse_octal_ascii acc width = match ((Char.code rdr#peek - Char.code '0'), width) with
      (_, 0) ->
        if acc <= 127 then
          Char.chr acc
        else
          raise (LexicalError (Printf.sprintf "Octal value out of ASCII range: [\\0%o]" acc))|
      (d, _) when d >=0 && d < 7 ->
        let _ = rdr#next in
        parse_octal_ascii (8 * acc + d) (width - 1)|
      _ ->
        if acc <= 127 then
          Char.chr acc
        else
          raise (LexicalError (Printf.sprintf "Octal value out of ASCII range: [\\0%o]" acc)) in
    parse_octal_ascii 0 3|
  _ ->
    raise (LexicalError "Expected octal digit");;
    
(*
  parse an ascii character expressed as a hexadecimal value (\xhh)
*)
let parse_hexa_ascii rdr = match rdr#peek with
  c when (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F') ->
    let rec parse_hexa_ascii acc width = match (rdr#peek, width) with
      (_, 0) ->
        if acc <= 127 then
          Char.chr acc
        else
          raise (LexicalError (Printf.sprintf "Hexa-decimal value out of ASCII range: [\\x%X]" acc))|
      (d, _) when d >= '0' && d <= '9' ->
        let _ = rdr#next in
        parse_hexa_ascii (16 * acc + (Char.code d - Char.code '0')) (width - 1)|
      (d, _) when d >= 'a' && d <= 'f' ->
        let _ = rdr#next in
        parse_hexa_ascii (16 * acc + (10 + Char.code d - Char.code 'a')) (width - 1)|
      (d, _) when d >= 'A' && d <= 'F' ->
        let _ = rdr#next in
        parse_hexa_ascii (16 * acc + (10 + Char.code d - Char.code 'A')) (width - 1)|
      _->
        (* there should be exactly 2 hexa-decimal digits *)
        raise (LexicalError (Printf.sprintf "Invalid hexa-decimal escape: [\\x%X]" acc)) in
    parse_hexa_ascii 0 2|
  _ ->
    raise (LexicalError "Expected hexa-decimal digit");;
    
(*
  parse an ascii control character expressed as a (Control +) key value
*)
let parse_control_ascii rdr = match rdr#next with
  '?' ->
    Char.chr 127|
  c when c >= '@' && c <= '_' ->
    Char.chr (Char.code c - Char.code '@')|
  _->
    raise (LexicalError "Expected ASCII control-character");;

(*
  creates a tokenizer object
*)
let make_tokenizer exp =
  let (mods, rexp_bounds) = extract_modifiers exp in
  let rdr = make_chreader exp rexp_bounds in
  let stk = Stack.create () in
  let ptk = ref EOS in
  (*
    specialized routine for tokenizing escape (\) directives
  *)
  let next_escaped () = match rdr#next with
    '0' -> Literal (parse_octal_ascii rdr)|
    'x' -> Literal (parse_hexa_ascii rdr)|
    'c' -> Literal (parse_control_ascii rdr)|
    't' -> Literal '\t'|
    'n' -> Literal '\n'|
    'r' -> Literal '\r'|
    'f' -> Literal '\x0C'|
    'a' -> Literal '\x07'|
    'e' -> Literal '\x1B'|
    'd' -> Class (Data.cls_digit)|
    'D' -> Class (Data.cls_ndigit)|
    's' -> Class (Data.cls_space)|
    'S' -> Class (Data.cls_nspace)|
    'w' -> Class (Data.cls_word)|
    'W' -> Class (Data.cls_nword)|
    'b' -> Anchor (Wordb)|
    'B' -> Anchor (NWordb)|
    'A' -> Anchor (BInput)|
    'z' -> Anchor (EInput)|
    '\x00' ->
      raise (LexicalError "Unexpected end of input")|
    'Q' ->
      let next_verbatim () = match rdr#next with
        '\\' when 'E' = rdr#peek ->
          let _ = rdr#next in
          let _ = Stack.pop stk in
          (Stack.top stk) ()|
        '\x00' ->
          raise (LexicalError "Incomplete quotated expression")|
        c ->
          Literal c in
      let _ = Stack.push next_verbatim stk in
      (Stack.top stk) ()|
    c ->
      if List.exists (fun x -> c = x) escapables then
        Literal c
      else
        raise (LexicalError (Printf.sprintf "Unknown directive: [\\%c]" c)) in
  (*
    routine tokenizing inside character classes : [...]
    reference: http://www.regular-expressions.info/charclass.html
  *)
  let next_class_token () = match rdr#next with
    '[' ->
      LSquare|
    '-' ->
      if !ptk = LSquare || !ptk = CNegate || rdr#peek = ']' then
        Literal '-'
      else
        CRange|
    '^' when !ptk = LSquare ->
      CNegate|
    ']' ->
      if !ptk = LSquare || !ptk = CNegate then
        Literal ']'
      else
        let _ = Stack.pop stk in
        RSquare|
    '\\' ->
      next_escaped ()|
    '\x00' ->
      raise (LexicalError "Incomplete character class definition")|
    c ->
      if c <= '\x7F' then
        Literal c
      else
        raise (LexicalError (Printf.sprintf "Non-ASCII input character: [%c]" c)) in
  (*
    tokenizing inside a range {m, n}
  *)
  let next_range_token () = match rdr#peek with
    '}' ->
      let _ = rdr#next in
      let _ = Stack.pop stk in
      RCurly|
    ',' ->
      let _ = rdr#next in
      Literal ','|  
    d when d >= '0' && d <= '9' ->
      Positive (parse_positive_decimal rdr)|  
    _ ->
      raise (LexicalError ("Invalid range specification")) in
  (*
    normal tokenizing routine
  *)
  let next_token () = match rdr#next with
    '|' -> VBar|
    '*' -> Asterix|
    '+' -> Plus|
    '?' -> QMark|
    '.' -> 
      if !(mods.dotall) then
        Class (Data.cls_dotall)
      else
        Class (Data.cls_dot)|
    '[' ->
      let _ = Stack.push next_class_token stk in
      LSquare|
    '{' ->
      let _ = Stack.push next_range_token stk in
      LCurly|
    '(' ->
      if rdr#peek <> '?' then
        LParen
      else (
        let _ = rdr#eat '?' in
        if rdr#peek <> ':' then
          (* the leading ? signals a special grouping construct *)
          raise (LexicalError (Printf.sprintf "Unsupported grouping construct: %c" rdr#next))
        else
          (* ?: signals a capturing group, ignore. *)
          let _ = rdr#eat ':' in
          LParen
      )|
    ')' -> 
      RParen|
    '^' -> 
      if !(mods.mline) then Anchor (BLine) else Anchor (BInput)|
    '$' -> 
      if !(mods.mline) then Anchor (ELine) else Anchor (EInput)|
    '\\' ->
      next_escaped ()|
    '\x00' -> EOS|
    c ->
      if c <= '\x7F' then
        Literal c
      else
        raise (LexicalError (Printf.sprintf "Non-ASCII input character: [%c]" c)) in
  (*
    create tokenizer object
  *)
  let _ = Stack.push next_token stk in
  let npos = ref 0 in
  let toks = 
    object (me)
      method next =
        let tk = !ptk in
        let _ = npos := rdr#hpos in
        let _ = ptk := (Stack.top stk) () in
        tk
      method peek = !ptk
      method eat tk =
        let cpos = !npos in
        if tk = me#next then
          me
        else
          raise (LexicalError (Printf.sprintf "Expected token [%s] at column: %d" (format_token tk) cpos))
      method hpos = !npos
      method mods = mods
      method rest = rdr#rest
    end in
  (* initialize stream - ptk is set to EOS initially *)
  toks#eat EOS;;
