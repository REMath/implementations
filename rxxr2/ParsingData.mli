(* © Copyright University of Birmingham, UK *)

(* lexing / parsing exceptions *)
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

(* parsing meta-data *)
type meta = {
  spos : int;
  epos : int;
  mutable scount : int; (* no.of states required *) 
  mutable nullable : bool;
  mutable cflags : int
};;

(* a pattern is a regex with a bunch of global modifiers *)
type pattern = (regex * int)
(* a regex is an expression plus some meta-data *)
and regex = (exp * meta)
(* expression *)
and exp = Zero (* null *)
  |One (* empty *)
  |Dot (* any *)
  |Pred of pred (* predicate *)
  |Atom of atom (* atom *)
  |Group of gkind * int * int * regex (* group *)
  |Backref of int (* backreference *)
  |Conc of regex * regex (* concatenation *)
  |Alt of regex * regex (* alternation *)
  |Kleene of qfier * regex (* repetition *)
(* expressions matching just a single character *)
and atom = Char of char (* single character *)
  |Cls of (char * char) list (* character class *)
(* predicate expressions - anchors *)
and pred = Bol (* beginning of line *)
  |Eol (* end of line *)
  |Wordb (* word boundary *)
  |NWordb (* not a word boundary *)
  |Boi (* beginning of input *)
  |Eom (* end of previous match *)
  |Eoi1 (* end of input, except the final terminator *)
  |Eoi2 (* end of input *)
(* different kinds of grouping constructs *)
and gkind = CAP of int (* capturing group with group id *)
  |NOCAP (* non-capturing group *)
  |MODS (* inline modifiers *)
  |PLA (* positive look-ahead *)
  |NLA (* negative look-ahead *)
  |PLB (* positive look-behind *)
  |NLB (* negative look-behind *)
  |ATOMIC (* atomic group *)
(* quantifiers *)
and qfier = Gq (* greedy *)
  |Rq;; (* reluctant *)

(* signals an error with a range expression e{m, n} *)
exception InvalidRangeDefinition of int * (int * int * qfier)

(* flags for regex lexer *)
val flg_unix_lines : int;;
val flg_no_case : int;;
val flg_multiline : int;;
val flg_dotall : int;;

(* create regex with default meta-data *)
val make_r : exp -> (int * int) -> regex;;
(* shorthand functions for querying regex meta-data *)
val r_spos : regex -> int;;
val r_epos : regex -> int;;
val r_pos : regex -> (int * int);;

(* a range-tree structure used to store character classes in sorted order *)
type ctr = CTNull | CTNode of char * char * ctr ref * ctr ref;;

(* insert new range into character class *)
val ctr_add : ctr -> char -> char -> ctr;;
(* read out the character class *)
val ctr_positive : ctr -> (char * char) list;;
(* read out the inverse of the character class *)
val ctr_negative : ctr -> (char * char) list;;
