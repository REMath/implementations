%{
(* © Copyright University of Birmingham, UK *)

open ParsingData

(* validate backreference *)
let re_evaluate_backref (i, pos) gcount =
  let rec rebuild r clist npos = match clist with
    [] -> r
    |c :: t -> rebuild (make_r (Conc (r, make_r (Atom (Char c)) (npos, npos))) (r_spos r, npos)) t (npos + 1) in
  let rec unparse j epos clist = match j with
    |_ when j <= gcount -> rebuild (make_r (Backref j) (fst pos, epos)) clist (epos + 1)
    |_ when j < 10 -> raise (ParsingData.InvalidBackreference (fst pos))
    |_ -> unparse (j / 10) (epos - 1) ((Char.chr (48 + (j mod 10))) :: clist) in
  unparse i (snd pos) [];;

(* assign capturing group identifiers and validate backreferences *)
let rec fix_captures r go gc = match (fst r) with
  Zero | One | Dot | Pred _ | Atom _ -> (r, gc)
  |Group (CAP _, m_on, m_off, r1) ->
    let (_r1, gc2) = fix_captures r1 (go + 1) gc in
    ((Group (CAP (go + 1), m_on, m_off, _r1), snd r), gc2 + 1)
  |Group (gkind, m_on, m_off, r1) ->
    let (_r1, gc2) = fix_captures r1 go gc in
    ((Group (gkind, m_on, m_off, _r1), snd r), gc2)
  |Backref i ->
    (re_evaluate_backref (i, r_pos r) gc, gc)
  |Conc (r1, r2) ->
    let (_r1, gc2) = fix_captures r1 go gc in
    let (_r2, gc3) = fix_captures r2 go gc2 in
    ((Conc (_r1, _r2), snd r), gc3) 
  |Alt (r1, r2) ->
    let (_r1, gc2) = fix_captures r1 go gc in
    let (_r2, gc3) = fix_captures r2 go gc in
    ((Alt (_r1, _r2), snd r), gc2 + (gc3 - gc))
  |Kleene (qf, r1) ->
    let (_r1, gc2) = fix_captures r1 go gc in
    ((Kleene (qf, _r1), snd r), gc2);;
  
%}

%token <(int * int) * ParsingData.regex> Regex
%token <int> Mod
%token Eos

%start parse
%type <ParsingData.pattern> parse
%%

parse: Eos { (make_r One (0, 0), 0) } 
  |Regex mods Eos { (fst (fix_captures (make_r (fst (snd $1)) (fst $1)) 0 0), $2) }

mods: { ParsingData.flg_dotall } /* POPL submission: DOT_ALL enabled by default */
  |Mod mods { $1 lor $2 }
