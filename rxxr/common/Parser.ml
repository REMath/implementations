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
open Lexer;;

(*
  used to flag syntax errors
*)
exception SyntaxError of string;;

(*
  used to flag parsing errors
*)
exception ParserError of string;;

(*
  counter for keeping track of node labels
*)
let ix =
  let count = ref 0 in
  object
    method next =
      let _ = count := !count + 1 in
      !count - 1
    method reset =
      count := 0
  end;;

(*
  function for backpatching a list of continuation pointers
*)
let rec backpatch l r = match l with
  [] ->
    ()|
  p :: t ->
    p := r; backpatch t r;;

(*
  context type used for parsing
*)
class context (r : regex) (rconts : regex ref list) (rsize : int) =
  object
    method r = r
    method conts = rconts
    method sz = rsize
  end;;

(*
  returns the concatenation of two contexts
*)
let concat ltx rtx =
  let _ = backpatch ltx#conts rtx#r in
  new context ltx#r rtx#conts (ltx#sz + rtx#sz);;

(*
  returns the alternation of two contexts
*)
let alter ltx rtx =
  let r = Alt (new mdata ix#next (meta ltx#r)#spos (meta rtx#r)#epos, ref ltx#r, ref rtx#r) in
  new context r (ltx#conts @ rtx#conts) (ltx#sz + rtx#sz + 1);;

(*
  returns the kleene of a context
*)
let kleene ltx qf toks =
  let k = ref End in
  (* kleene expressions point to the entire repetition expression in the input stirng *)
  let r = Kleene (new mdata ix#next (meta ltx#r)#spos toks#hpos, qf, ref ltx#r, k) in
  let _ = backpatch ltx#conts r in
  new context r [k] (ltx#sz + 1);;

(*
  adjusts the boundaries of the regex node wrapped in the given context
  this is required for handling parenthesized expressions (E)
*)
let set_boundaries ctx spos' epos' =
  let nr = match ctx#r with
    End -> End|
    Empty (m, k) -> Empty (new mdata m#id spos' epos', k)|
    Data.Anchor (m, b, k) -> Data.Anchor (new mdata m#id spos' epos', b, k)|
    Atom (m, a, k) -> Atom (new mdata m#id spos' epos', a, k)| 
    Alt (m, pl, pr) -> Alt (new mdata m#id spos' epos', pl, pr)|
    Kleene (m, qf, p, k) -> Kleene (new mdata m#id spos' epos', qf, p, k) in
  new context nr ctx#conts ctx#sz;;

(*
  creates a clone of a regex node
*)
let clone ltx = match ltx#r with
  End ->
    raise (ParserError "CLONE: End node should not be cloned")|
  _->
    let ht = Hashtbl.create ltx#sz in
    let rec clone' r = 
      let idx = (meta r)#id in
      if r <> End && Hashtbl.find_all ht idx <> [] then
        let k = ref (Hashtbl.find ht idx) in
        (k, [])
      else match r with
        End ->
          let k = ref End in
          (k, [k])|
        Empty (m, k) ->
          let (kclone, conts) = clone' !k in
          let rclone = Empty (new mdata ix#next m#spos m#epos, kclone) in
          let _ = Hashtbl.add ht idx rclone in
          (ref rclone, conts)|
        Data.Anchor (m, b, k) ->
          let (kclone, conts) = clone' !k in
          let rclone = Data.Anchor (new mdata ix#next m#spos m#epos, b, kclone) in
          let _ = Hashtbl.add ht idx rclone in
          (ref rclone, conts)|
        Atom (m, atm, k) ->
          let (kclone, conts) = clone' !k in
          let rclone = Atom (new mdata ix#next m#spos m#epos, atm, kclone) in
          let _ = Hashtbl.add ht idx rclone in
          (ref rclone, conts)|
        Alt (m, pl, pr) ->
          let (pl_clone, pl_conts) = clone' !pl in
          let (pr_clone, pr_conts) = clone' !pr in
          let rclone = Alt (new mdata ix#next m#spos m#epos, pl_clone, pr_clone) in
          let _ = Hashtbl.add ht idx rclone in
          (ref rclone, pl_conts @ pr_conts)|
        Kleene (m, qf, p, k) ->
          let (kclone, conts) = clone' !k in
          let pdummy = ref End in
          let rclone = Kleene (new mdata ix#next m#spos m#epos, qf, pdummy, kclone) in
          let _ = Hashtbl.add ht idx rclone in
          let (pclone, _) = clone' !p in
          let _ = pdummy := !pclone in
          (ref rclone, conts) in
    let (p, conts) = clone' ltx#r in
    new context !p conts ltx#sz;;

(*
  creates a chain of regex clones of the specified length (excluding the input)
*)
let rec chain ltx n = match n with
  1 ->
    clone ltx|
  n when n > 1 ->
    let ctx = clone ltx in
    let ntx' = chain ltx (n - 1) in
    concat ctx ntx'|
  _->
    raise (ParserError "CHAIN: Invalid chain length");;

(*
  creates a regex for the range {0, n} (includes the input)
*)
let rec zton ltx n qf = match n with
  1 ->
    let k = ref End in
    (* all generated regexes point to the original repeated expression in the input string *)
    let rtx = new context (Empty (new mdata ix#next (meta ltx#r)#spos (meta ltx#r)#epos, k)) [k] 1 in
    if qf = Gq then alter ltx rtx else alter rtx ltx|
  n when n > 1 ->
    let ntx = chain ltx n in
    let ntx' = zton ltx (n - 1) qf in
    if qf = Gq then alter ntx ntx' else alter ntx' ntx|
  _->
    raise (ParserError "ZTON: Invalid range length");;

(*
  creates a regex for the range {m, n} (includes the input)
*)
let mton ltx (mn, qf) toks = match mn with
  (0, -1) ->
    kleene ltx qf toks|
  (m, -1) when m > 0 ->
    let mtx = chain ltx m in
    let ntx = kleene ltx qf toks in
    concat mtx ntx|
  (0, n) when n > 0 ->
    zton ltx n qf|
  (1, 1) ->
    ltx|
  (m, n) when m > 1 && m = n ->
    let rtx = chain ltx (m - 1) in 
    concat ltx rtx|
  (m, n) when m > 0 && m < n ->
    let mtx = chain ltx m in
    concat mtx (zton ltx (n - m) qf)|
  _ ->
    raise (ParserError "MTON: Invalid range");;
      
(*
  functions for parsing a regex string into a Thompson NFA
*)
let rec parse_thompson exp =
  let parse_thompson' toks =
    let _ = ix#reset in
    let ctx = parse_expression toks in
    match toks#peek with
      EOS ->
        (ctx#r, ctx#conts, ctx#sz)|
      _ ->
        raise (SyntaxError (Printf.sprintf "Trailing tokens: %s" toks#rest)) in
  parse_thompson' (Lexer.make_tokenizer exp) 
(* E := BE' *)
and parse_expression toks =
  parse_expression' (parse_branch toks) toks
(* E' = +BE' *)
and parse_expression' ltx toks = match toks#peek with
  VBar ->
    parse_expression' (alter ltx (parse_branch (toks#eat VBar))) toks|
  _ ->
    ltx
(* B := FB' *)
and parse_branch toks =
  parse_branch' (parse_factor toks) toks
(* B' = FB' | ε *)
and parse_branch' ltx toks = match toks#peek with
  LParen | Anchor _ | Literal _ | LSquare | Class _ ->
    parse_branch' (concat ltx (parse_factor toks)) toks|
  _ ->
    ltx
(* F := AF' *)
and parse_factor toks =
  parse_factor' (parse_atom toks) toks
(* F' := RF' | ε *)
and parse_factor' ltx toks = match toks#peek with
  Asterix | Plus | QMark | LCurly ->
    parse_factor' (mton ltx (parse_range toks) toks) toks|
  _ ->
    ltx
(* A := () | Anchor | a | [C] | (E) *)
and parse_atom toks = 
  let bpos = toks#hpos in
  match toks#next with
    Anchor b ->
      let k = ref End in
      new context (Data.Anchor (new mdata ix#next bpos toks#hpos, b, k)) [k] 1|
    Literal c ->
      let k = ref End in
      if !(toks#mods.icase) then
        let c_upper = Char.uppercase c in
        if c <> c_upper then
          new context (Atom (new mdata ix#next bpos toks#hpos, Data.Class [(c_upper, c_upper); (c, c)], k)) [k] 1
        else (
          let c_lower = Char.lowercase c in
          if c <> c_lower then
            new context (Atom (new mdata ix#next bpos toks#hpos, Data.Class [(c, c); (c_lower, c_lower)], k)) [k] 1
          else
            new context (Atom (new mdata ix#next bpos toks#hpos, Char c, k)) [k] 1
        )
      else
        new context (Atom (new mdata ix#next bpos toks#hpos, Char c, k)) [k] 1|
    Class rlist ->
      let k = ref End in
      new context (Atom (new mdata ix#next bpos toks#hpos, Data.Class rlist, k)) [k] 1|
    LSquare ->
      let k = ref End in
      new context (Atom (new mdata ix#next bpos toks#hpos, Data.Class (assemble_class toks), k)) [k] 1|
    LParen -> begin
      match toks#peek with
        RParen ->
          let _ = toks#eat RParen in
          let k = ref End in
          new context (Empty (new mdata ix#next bpos toks#hpos, k)) [k] 1|
        _ ->
          let ctx = parse_expression toks in
          let _ = toks#eat RParen in
          set_boundaries ctx bpos toks#hpos
    end|
    _ ->
      raise (SyntaxError (Printf.sprintf "Unexpected token at column: %d" bpos))
(*
  assemble a character-class from a sequence of tokens
*)
and assemble_class toks =
  let rec parse_class rlist = match toks#next with
    Literal c ->
      if toks#peek = CRange then
        let _ = toks#next in
        match toks#next with
          Literal d ->
            parse_class (rlist @ [(c, d)])|
          _ ->
            raise (LexicalError "Invalid character class definition")
      else
        parse_class (rlist @ [(c, c)])|
    Class cls ->
      parse_class (rlist @ cls)|
    RSquare ->
      Util.normalize_class rlist !(toks#mods.icase)|
    _ ->
      raise (LexicalError "Invalid character class definition") in
  match toks#peek with
    CNegate ->
      let _ = toks#next in
      Util.negate_class (parse_class [])|
    _ ->
      parse_class []
(* R := *R' | +R' | ?R' | {m}R' | {m,}R' | {m, n}R' *)
and parse_range toks = match toks#next with
  Asterix ->
    parse_qfier (0, -1) toks|
  Plus ->
    parse_qfier (1, -1) toks|
  QMark ->
    parse_qfier (0, 1) toks|
  LCurly -> begin
    match toks#next with
      Positive m -> begin
        match toks#next with
          Literal ',' -> begin
            match toks#next with
              Positive n when n > 0 && m <= n ->
                let _ = toks#eat RCurly in
                parse_qfier (m, n) toks|
              RCurly ->
                parse_qfier (m, -1) toks|
              _ ->
                raise (SyntaxError "Invalid range specification")
          end|
          RCurly when m > 0 ->
            parse_qfier (m, m) toks|
          _ ->
            raise (SyntaxError "Invalid range specification")
      end|
      _ ->
        raise (SyntaxError "Invalid range specification")
  end|
  _->
    raise (SyntaxError "Invalid range specification")
(* R' := ? | + | ε *)
and parse_qfier rng toks = match toks#peek with
  QMark ->
    let _ = toks#eat QMark in
    (rng, Rq)|
  Plus ->
    raise (SyntaxError "Unsupported possessive quantifier")|
  _ ->
    (rng, Gq);;
