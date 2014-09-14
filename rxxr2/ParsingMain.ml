(* © Copyright University of Birmingham, UK *)

open ParsingData

(* different states of the pattern lexer *)
type plstate = {mutable pl_phase : plphase}
and plphase = PATTERN | MODS;;

(* switch between different lexing functions based on the current state / token *)
let create_pattern_lexer_decorator () =
  let state = { pl_phase = PATTERN } in
  let lex_pattern_stateful lbuf = match state.pl_phase with
    PATTERN ->
      let _ = state.pl_phase <- MODS in
      PatternLexer.tk_normal lbuf
    |MODS ->
      PatternLexer.tk_mods lbuf in
  lex_pattern_stateful;; 

let parse_pattern lexbuf = PatternParser.parse (create_pattern_lexer_decorator ()) lexbuf;;
