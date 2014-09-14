%{
(* © Copyright University of Birmingham, UK *)

open ParsingData

(* insert entire character class into a ctr tree *)
let ctr_add_cls tr cls = List.fold_left (fun tr (u, v) -> ctr_add tr u v) tr cls;;

(* make a sequence of n copies of a given regex *)
let rec make_seq r n cpos = match n with
  1 -> r
  |n2 when n2 > 1 -> make_r (Conc (r, make_seq r (n - 1) cpos)) cpos
  |_-> raise ParsingData.InternalParsingError;;

(* make e{0, n} greedy *)
let rec make_greedy_zton r n cpos = match n with
  -1 -> make_r (Kleene (Gq, r)) cpos 
  |1 -> make_r (Alt (r, make_r One cpos)) cpos
  |n2 when n2 > 1 -> make_r (Alt (make_seq r n cpos, make_greedy_zton r (n - 1) cpos)) cpos
  |_-> raise ParsingData.InternalParsingError;;

(* make e{0, n} reluctant *)
let rec make_reluctant_zton r n cpos = match n with
  -1 -> make_r (Kleene (Rq, r)) cpos 
  |1 -> make_r (Alt (make_r One cpos, r)) cpos
  |n2 when n2 > 1 -> make_r (Alt (make_reluctant_zton r (n - 1) cpos, make_seq r n cpos)) cpos
  |_-> raise ParsingData.InternalParsingError;;

(* make e{m, n} *)
let rec make_range r rng cpos = match rng with
  (0, 0, _) -> make_r One cpos
  |(0, -1, qf) -> make_r (Kleene (qf, r)) cpos
  |(m, -1, qf) -> make_r (Conc (make_seq r m cpos, make_range r (0, -1, qf) cpos)) cpos
  |(0, n, Gq) -> make_greedy_zton r n cpos
  |(0, n, Rq) -> make_reluctant_zton r n cpos
  |(m, n, _) when m = n -> make_seq r m cpos
  |(m, n, qf) when m < n -> make_r (Conc (make_seq r m cpos, make_range r (0, (n - m), qf) cpos)) cpos
  |_ -> raise (ParsingData.InvalidRangeDefinition(snd cpos, rng))

%}

%token <(int * int) * char> Literal
%token <(int * int) * ParsingData.pred> Anchor
%token <int * ParsingData.gkind> GrpOpen
%token <(int * int)> BeginQuote EndQuote
%token <int> TkDot ModsGrpOpen Mod GrpClose ClsClose 
%token <(int * int) * int> TkBackref
%token <int * bool> ClsOpen
%token <char * char> ClsRange
%token <(int * int) * ((char * char) list)> ClsNamed
%token <int * (int * int * ParsingData.qfier)> Repetition
%token VBar NegMods EndMods Eos

%start parse
%type <ParsingData.regex> parse
%%

parse: Eos { make_r One (0, 0) } 
  |expr Eos { $1 };

expr: conc { $1 } 
  |conc VBar expr { make_r (Alt ($1, $3)) (r_spos $1, r_epos $3) }

conc: factor { $1 }
  |factor conc { make_r (Conc ($1, $2)) (r_spos $1, r_epos $2) }

factor: atom { $1 }
  |factor Repetition { make_range $1 (snd $2) (r_spos $1, fst $2) }

atom: literal { $1 }
  |Anchor { make_r (Pred (snd $1)) (fst $1) }
  |TkDot { make_r Dot ($1, $1) }
  |BeginQuote EndQuote { make_r One (fst $1, snd $2) }
  |BeginQuote quote_body EndQuote { $2 }
  |GrpOpen GrpClose { make_r (Group (snd $1, 0, 0, make_r One (fst $1, $2))) (fst $1, $2) }
  |GrpOpen expr GrpClose { make_r (Group (snd $1, 0, 0, $2)) (fst $1, $3) }
  |TkBackref { make_r (Backref (snd $1)) (fst $1) }
  |ModsGrpOpen mods GrpClose { make_r (Group (MODS, fst $2, snd $2, make_r One ($1, $3))) ($1, $3) }
  |ModsGrpOpen mods EndMods GrpClose { make_r One ($1, $4) }
  |ModsGrpOpen mods EndMods expr GrpClose { make_r (Group (NOCAP, fst $2, snd $2, $4)) ($1, $5) }
  |ClsOpen ch_range_list ClsClose {
    let p = (fst $1, $3) in 
      if snd $1 then
        make_r (Atom (Cls (ctr_negative $2))) p 
      else 
        make_r (Atom (Cls (ctr_positive $2))) p
  }
  |ClsNamed { make_r (Atom (Cls (snd $1))) (fst $1) }

quote_body: literal { $1 }
  | literal quote_body { make_r (Conc ($1, $2)) (r_spos $1, r_epos $2)  }

literal: Literal { make_r (Atom (Char (snd $1))) (fst $1) }

mods: mod_list { ($1, 0) }
  |mod_list NegMods mod_list {($1, $3) }

mod_list: { 0 }
  |Mod mod_list { $1 lor $2 }

ch_range_list: ch_range { ctr_add_cls CTNull $1 }
  |ch_range ch_range_list { ctr_add_cls $2 $1 }

ch_range: Literal { [(snd $1, snd $1)] }
  |ClsRange { [$1] }
  |ClsNamed { snd $1 }
