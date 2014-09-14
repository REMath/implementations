(* © Copyright University of Birmingham, UK *)

open ParsingData
open Common

exception UnsupportedGroupingConstruct of int

type p = 
  |P_BOI
  |P_EOI
  |P_EOIX of bool
  |P_BOL of bool
  |P_EOL of bool
  |P_EOM
  |P_WB
  |P_NWB;;

type s =
  |End
  |Kill
  |Pass of int
  |MakeB of int
  |EvalB of int
  |Match of (char * char) list * int
  |CheckPred of p * int
  |CheckBackref of int * int
  |BeginCap of int * int
  |EndCap of int * int
  |BranchAlt of int * int
  |BranchKln of bool * int * int;;

type t = {
  (* states are store in an array, each array index identifies a state *)
  states : s array; 
  (* an ordered list of transitions corresponding to each state - lazily initialized *)
  transitions : (char * char * int) list option array; 
  (* sub-expression positions corresponding to each state *)
  positions : (int * int) array; 
  (* root state index *)
  root : int 
};;

(* convert flags to predicate type *)
let get_pcond pd flags = match pd with
  Boi -> P_BOI
  |Eom -> P_EOM
  |Eoi1 -> P_EOIX (flags land flg_unix_lines != 0)
  |Eoi2 -> P_EOI
  |Bol -> if (flags land flg_multiline != 0) then P_BOL (flags land flg_unix_lines != 0) else P_BOI
  |Eol -> if (flags land flg_multiline != 0) then P_EOL (flags land flg_unix_lines != 0) else P_EOI
  |Wordb -> P_WB
  |NWordb -> P_NWB;; 

(* analyse the regex AST and calculate various attributes *)
let rec decorate_regex r flags = match (fst r) with
  Zero ->
    (snd r).scount <- 1;
    (snd r).nullable <- false;
    (snd r).cflags <- flags;
  |One ->
    (snd r).scount <- 1;
    (snd r).nullable <- true;
    (snd r).cflags <- flags;
  |Dot ->
    (snd r).scount <- 1;
    (snd r).nullable <- false;
    (snd r).cflags <- flags;
  |Pred _ ->
    (snd r).scount <- 1;
    (snd r).nullable <- true;
    (snd r).cflags <- flags;
  |Atom _ ->
    (snd r).scount <- 1;
    (snd r).nullable <- false;
    (snd r).cflags <- flags;
  |Backref _ ->
    (snd r).scount <- 1;
    (snd r).nullable <- true;
    (snd r).cflags <- flags;
  |Group (MODS, m_on, m_off, _) ->
    let flags2 = (flags lor m_on) land (lnot m_off) in
    (snd r).scount <- 0;
    (snd r).nullable <- true;
    (snd r).cflags <- flags2;
  |Group (CAP _, _, _, r1) ->
    decorate_regex r1 flags;
    (snd r).scount <- 2 + (snd r1).scount;
    (snd r).nullable <- (snd r1).nullable;
    (snd r).cflags <- flags;
  |Group (NOCAP, m_on, m_off, r1) ->
    let flags2 = (flags lor m_on) land (lnot m_off) in
    decorate_regex r1 flags2;
    (snd r).scount <- (snd r1).scount;
    (snd r).nullable <- (snd r1).nullable;
    (snd r).cflags <- flags;
  |Group (_) -> raise (UnsupportedGroupingConstruct (r_spos r))
  |Conc (r1, r2) ->
    decorate_regex r1 flags;
    decorate_regex r2 (snd r1).cflags;
    (snd r).scount <- (snd r1).scount + (snd r2).scount;
    (snd r).nullable <- (snd r1).nullable && (snd r2).nullable;
    (snd r).cflags <- (snd r2).cflags;
  |Alt (r1, r2) ->
    decorate_regex r1 flags;
    decorate_regex r2 (snd r1).cflags;
    (snd r).scount <- 1 + (snd r1).scount + (snd r2).scount;
    (snd r).nullable <- (snd r1).nullable || (snd r2).nullable;
    (snd r).cflags <- (snd r2).cflags;
  |Kleene (_, r1) ->
    let n = decorate_regex r1 flags; if (snd r1).nullable then 3 else 1 in
    (snd r).scount <- n + (snd r1).scount;
    (snd r).nullable <- true;
    (snd r).cflags <- (snd r1).cflags;
  ;;

(* recursively compile a regex into NFA - state vector is filled in reverse *)
let rec compile r sv pv next kont flags = match (fst r) with
  Zero ->
    pv.(next) <- r_pos r;
    sv.(next) <- Kill;
    (next - 1, next)
  |One ->
    pv.(next) <- r_pos r;
    sv.(next) <- Pass (kont);
    (next - 1, next)
  |Dot ->
    pv.(next) <- r_pos r;
    if (flags land flg_dotall) != 0 then
      sv.(next) <- Match ([('\x00', '\x7f')], kont)
    else if (flags land flg_unix_lines) != 0 then
      sv.(next) <- Match ([('\x00', '\x09'); ('\x0b', '\x7f')], kont)
    else
      sv.(next) <- Match ([('\x00', '\x09'); ('\x0b', '\x0c'); ('\x0e', '\x7f')], kont);
    (next - 1, next)
  |Atom (Char c) ->
    pv.(next) <- r_pos r;
    if (flags land flg_no_case) != 0 then
      sv.(next) <- Match (chr_ignore_case c, kont)
    else
      sv.(next) <- Match ([(c, c)], kont);
    (next - 1, next)
  |Atom (Cls cls) ->
    pv.(next) <- r_pos r;
    if (flags land flg_no_case) != 0 then
      sv.(next) <- Match (cls_ignore_case cls, kont)
    else
      sv.(next) <- Match (cls, kont);
    (next - 1, next)
  |Pred p ->
    pv.(next) <- r_pos r;
    sv.(next) <- CheckPred (get_pcond p flags, kont);
    (next - 1, next)
  |Backref i -> 
    pv.(next) <- r_pos r;
    sv.(next) <- CheckBackref (i, kont);
    (next - 1, next)
  |Group (CAP i, _, _, r1) ->
    pv.(next) <- (r_epos r, r_epos r);
    sv.(next) <- EndCap (i, kont);
    let (next, kont) = compile r1 sv pv (next - 1) next flags in
    pv.(next) <- (r_spos r, r_spos r);
    sv.(next) <- BeginCap (i, kont);
    (next - 1, next)
  |Group (MODS, m_on, m_off, _) ->
    (next, kont)
  |Group (NOCAP, m_on, m_off, r1) ->
    let flags2 = (flags lor m_on) land (lnot m_off) in
    compile r1 sv pv next kont flags2
  |Group (_) -> raise (UnsupportedGroupingConstruct (r_spos r))
  |Conc (r1, r2) ->
    let (next, kont) = compile r2 sv pv next kont (snd r1).cflags in
    compile r1 sv pv next kont flags
  |Alt (r1, r2) ->
    let (next, kont_r2) = compile r2 sv pv next kont (snd r1).cflags in
    let (next, kont_r1) = compile r1 sv pv next kont flags in
    pv.(next) <- r_pos r;
    sv.(next) <- BranchAlt (kont_r1, kont_r2);
    (next - 1, next)
  |Kleene (qf, r1) ->
    let (next_o, kont_o) = (next, kont) in
    let (next_eb, kont_eb) = if (snd r1).nullable then (
      pv.(next_o - 1) <- (r_epos r1, r_epos r1);
      sv.(next_o - 1) <- EvalB (next_o);
      (next_o - 2, next_o - 1)
    ) else (
      (next_o - 1, next_o)
    ) in
    let (next_r1, kont_r1) = compile r1 sv pv next_eb kont_eb flags in
    let (next_mb, kont_mb) = if (snd r1).nullable then (
      pv.(next_r1) <- (r_spos r1, r_spos r1);
      sv.(next_r1) <- MakeB (kont_r1);
      (next_r1 - 1, next_r1)
    ) else (
      (next_r1, kont_r1)
    ) in
    pv.(next_o) <- r_pos r;
    sv.(next_o) <- BranchKln (qf == Gq, kont_mb, kont_o);
    (next_mb, next_o);;

let make (r, flags) =
  let _ = decorate_regex r flags in 
  let state_count = (snd r).scount + 1 in (* + 1 for the final state *)
  let sv = Array.create state_count End in
  let tv = Array.create state_count None in
  let pv = Array.create state_count (r_epos r, r_epos r) in
  let (_, kont) = compile r sv pv (state_count - 2) (state_count - 1) flags in
  {states = sv; transitions = tv; positions = pv; root = kont};;

let root nfa = nfa.root;;

let size nfa = Array.length nfa.states;;

let get_state nfa i = nfa.states.(i);;

let get_transitions nfa i =
  let rec explore i (st, lst) =
    if IntSet.mem i st then (st, lst) else
      let st = IntSet.add i st in
      match get_state nfa i with
        |End | Kill -> (st, lst)
        |Pass j -> explore j (st, lst)
        |MakeB j -> explore j (st, lst)
        |EvalB j -> explore j (st, lst)
        |Match (cls, j) -> (st, List.fold_left (fun l (u, v) -> (u, v, j) :: l) lst cls)
        |CheckPred _ -> (st, lst) (* not supported *)
        |CheckBackref _ -> (st, lst) (* not supported *)
        |BeginCap (_, j) -> explore j (st, lst)
        |EndCap (_, j) -> explore j (st, lst)
        |BranchAlt (j, k) -> explore j (explore k (st, lst))
        |BranchKln (gd, j, k) ->
          (* quantifiers affect the ordering of transitions *)
          if gd then
            explore k (explore j (st, lst))
          else
            explore j (explore k (st, lst)) in
  match nfa.transitions.(i) with
    |Some lst -> lst
    |None ->
      let (_, lst) = explore i (IntSet.empty, []) in
      nfa.transitions.(i) <- Some lst; lst;;

let get_subexp_location nfa i = nfa.positions.(i);;
