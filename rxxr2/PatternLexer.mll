(* © Copyright University of Birmingham, UK *)

{
open ParsingData
open PatternParser

(* different states of the regex lexer *)
type rlstate = {mutable rl_phase : rlphase}
and rlphase = REGEX_BODY | CLS_HEAD | CLS_BODY | MODS_LIST | QUOTE;;

(* switch between different lexing functions based on the current state / token *)
let create_regex_lexer_decorator () =
  let state = { rl_phase = REGEX_BODY } in
  let rec lex_regex_stateful lbuf = match state.rl_phase with
    REGEX_BODY ->
      begin
        let tk = RegexLexer.tk_normal lbuf in
        let _ = match tk with
          RegexParser.ClsOpen(_) -> state.rl_phase <- CLS_HEAD
          |RegexParser.ModsGrpOpen(_) -> state.rl_phase <- MODS_LIST
          |RegexParser.BeginQuote(_) -> state.rl_phase <- QUOTE
          |_ -> () in tk
      end
    |CLS_HEAD ->
      let _ = state.rl_phase <- CLS_BODY in
      RegexLexer.tk_class_header lbuf
    |CLS_BODY ->
      begin
        let tk = RegexLexer.tk_class_body lbuf in
        let _ = match tk with
          RegexParser.ClsClose(_) -> state.rl_phase <- REGEX_BODY
          |_ -> () in tk
      end
    |MODS_LIST ->
      begin
        let tk = RegexLexer.tk_mods_head lbuf in
        let _ = match tk with
          RegexParser.GrpClose(_) -> state.rl_phase <- REGEX_BODY
          |RegexParser.EndMods -> state.rl_phase <- REGEX_BODY
          |_ -> () in tk
      end
    |QUOTE ->
      begin
        let tk = RegexLexer.tk_quote lbuf in
        let _ = match tk with
          RegexParser.EndQuote(_) -> state.rl_phase <- REGEX_BODY
          |_ -> () in tk
      end in
  lex_regex_stateful;;

(* method for parsing the inner regex of /REGEX/MODS *)
let parse_regex r_str =
  let lexbuf = Lexing.from_string (Printf.sprintf "%s\n" r_str) in
  RegexParser.parse (create_regex_lexer_decorator ()) lexbuf;;

(* map of possible global modifers *)
let flg_map = Hashtbl.create 8;;
Hashtbl.add flg_map 'd' ParsingData.flg_unix_lines;;
Hashtbl.add flg_map 'i' ParsingData.flg_no_case;;
Hashtbl.add flg_map 'm' ParsingData.flg_multiline;;
Hashtbl.add flg_map 's' ParsingData.flg_dotall;;
(* greedy / reluctant quantifiers don't matter for ReDoS *)
Hashtbl.add flg_map 'G' 0;;
(* snort specific modifiers that we don't care about *)
Hashtbl.add flg_map 'R' 0;;
Hashtbl.add flg_map 'U' 0;;
Hashtbl.add flg_map 'P' 0;;
Hashtbl.add flg_map 'H' 0;;
Hashtbl.add flg_map 'D' 0;;
Hashtbl.add flg_map 'M' 0;;
Hashtbl.add flg_map 'C' 0;;
Hashtbl.add flg_map 'K' 0;;
Hashtbl.add flg_map 'S' 0;;
Hashtbl.add flg_map 'B' 0;;
Hashtbl.add flg_map 'O' 0;;

(* resolve global modifier *)
let get_flag c cpos =
  try
    Hashtbl.find flg_map c
  with Not_found ->
    raise (ParsingData.UnsupportedGlobalModifier(cpos, c));;

(* functions for querying token position *)
let get_pos lbuf = (Lexing.lexeme_start lbuf, Lexing.lexeme_end lbuf - 1);;
let get_spos lbuf = Lexing.lexeme_start lbuf;;
let get_epos lbuf = Lexing.lexeme_end lbuf - 1;;
}

rule tk_normal =
  parse '\n' { Eos }
    |'/' ([^'\n']* as r_str) '/' { Regex(get_pos lexbuf, parse_regex r_str) }
    |[^'/'][^'\n']* as r_str { Regex(get_pos lexbuf, parse_regex r_str) }
    |'/' { raise (ParsingData.UnbalancedPatternMarker(get_spos lexbuf)) }
    |eof { raise ParsingData.UnexpectedEndOfInput }
and tk_mods =
  parse '\n' { Eos }
    |_ as c { Mod(get_flag c (get_spos lexbuf)) }
    |eof { raise ParsingData.UnexpectedEndOfInput }
