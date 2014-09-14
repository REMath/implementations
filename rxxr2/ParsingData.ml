(* © Copyright University of Birmingham, UK *)

exception NonAsciiInput of int * char
exception UnsupportedInlineModifier of int * char
exception UnsupportedGlobalModifier of int * char
exception UnsupportedEscape of int * char
exception UnsupportedPossessiveQuantifier of int
exception IncompleteRangeDefinition of int
exception UnbalancedPatternMarker of int
exception InvalidBackreference of int
exception UnexpectedEndOfInput
exception InternalLexingError
exception InternalParsingError

type meta = {
  spos : int;
  epos : int;
  mutable scount : int;
  mutable nullable : bool;
  mutable cflags : int
};;

type pattern = (regex * int)
and regex = (exp * meta)
and exp = Zero 
  |One
  |Dot 
  |Pred of pred
  |Atom of atom
  |Group of gkind * int * int * regex
  |Backref of int
  |Conc of regex * regex       
  |Alt of regex * regex
  |Kleene of qfier * regex
and atom = Char of char
  |Cls of (char * char) list
and pred = Bol
  |Eol
  |Wordb
  |NWordb
  |Boi
  |Eom
  |Eoi1
  |Eoi2
and gkind = CAP of int
  |NOCAP
  |MODS
  |PLA
  |NLA
  |PLB
  |NLB
  |ATOMIC
and qfier = Gq
  |Rq;;

exception InvalidRangeDefinition of int * (int * int * qfier)

let flg_unix_lines  = 1;;
let flg_no_case  = 2;;
let flg_multiline  = 4;;
let flg_dotall  = 8;;

let make_r e (i, j) = (e, {spos = i; epos = j; scount = 0; nullable = false; cflags = 0});;
let r_spos r = (snd r).spos;;
let r_epos r = (snd r).epos;;
let r_pos r = (r_spos r, r_epos r);;

(* duplicated from Common.ml *)
let zmin = '\x00';;
let zmax = '\x7f';;
let zprev u = if u <= zmin then zmin else Char.chr (Char.code u - 1);;
let znext u = if u >= zmax then zmax else Char.chr (Char.code u + 1);;

type ctr = CTNull | CTNode of char * char * ctr ref * ctr ref;;

let ctr_add ctr u v =
  let rec ctr_add ctr u' v' = match ctr with
    CTNull -> CTNode(u', v', ref CTNull, ref CTNull)
    |CTNode(u, _, lt, _) when v' < u -> let _ = lt := ctr_add !lt u' v' in ctr
    |CTNode(_, v, _, rt) when v < u' -> let _ = rt := ctr_add !rt u' v' in ctr
    |CTNode(u, v, lt, rt) ->
      let _ = if u <> u' then
        lt := ctr_add !lt (min u u') (zprev (max u u')) in
      let _ = if v <> v' then
        rt := ctr_add !rt (znext (min v v')) (max v v') in
      CTNode(max u u', min v v', lt, rt) in
  if u > v then
    ctr_add ctr v u
  else
    ctr_add ctr u v;;

let ctr_positive ctr =
  let rec ctr_positive ctr lst = match ctr with
    CTNull -> lst
    |CTNode(u, v, lt, rt) -> match ctr_positive !rt lst with
      [] -> ctr_positive !lt [(u, v)]
      |(u', v') :: t when znext v == u' -> ctr_positive !lt ((u, v') :: t)
      | t -> ctr_positive !lt ((u, v) :: t) in 
  ctr_positive ctr [];;

let ctr_negative ctr = 
  let rec ctr_negative ctr neg next = match ctr with
    CTNull -> (neg, next)
    |CTNode(u, v, lt, rt) -> match ctr_negative !rt neg next with
      (neg2, next2) when v == zprev next2 -> ctr_negative !lt neg2 u
      |(neg2, next2) -> ctr_negative !lt ((znext v, zprev next2) :: neg2) u in
  let (neg, next) = ctr_negative ctr [] '\x80' in
    if zmin < next then
      (zmin, zprev next) :: neg
    else
      neg;;
