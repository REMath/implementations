(* © Copyright University of Birmingham, UK *)

{
open RegexParser

(* resolve pre-define character classes into (char * char) list representation *)
let resolve_class cls_str = match cls_str with
  "\\d" | "\\p{Digit}" -> [ ('\x30', '\x39') ]
  |"\\D" -> [ ('\x00', '\x2f'); ('\x3a', '\x7f') ]
  |"\\s" | "\\p{Space}"-> [ ('\x09', '\x0d'); ('\x20', '\x20') ]
  |"\\S" -> [ ('\x00', '\x08'); ('\x0e', '\x1f'); ('\x21', '\x7f') ]
  |"\\w" -> [ ('\x30', '\x39'); ('\x41', '\x5a'); ('\x5f', '\x5f'); ('\x61', '\x7a') ]
  |"\\W" -> [ ('\x00', '\x2f'); ('\x3a', '\x40'); ('\x5b', '\x5e'); ('\x60', '\x60'); ('\x7b', '\x7f') ]
  |"\\p{Lower}" -> [ ('\x61', '\x7a') ]
  |"\\p{Upper}" -> [ ('\x41', '\x5a') ]
  |"\\p{ASCII}" -> [ ('\x00', '\x7f') ]
  |"\\p{Alpha}" -> [ ('\x41', '\x5a'); ('\x61', '\x7a') ]
  |"\\p{Alnum}" -> [ ('\x30', '\x39'); ('\x41', '\x5a'); ('\x61', '\x7a') ]
  |"\\p{Punct}" -> [ ('\x21', '\x2f'); ('\x3a', '\x40'); ('\x5b', '\x60'); ('\x7b', '\x7e') ]
  |"\\p{Graph}" | "\\p{Print}" -> [ ('\x21', '\x7e') ]
  |"\\p{Blank}" -> [ ('\x09', '\x09'); ('\x20', '\x20') ]
  |"\\p{Cntrl}" -> [ ('\x00', '\x1f'); ('\x7f', '\x7f') ]
  |"\\p{XDigit}" -> [ ('\x30', '\x39'); ('\x41', '\x46'); ('\x61', '\x66') ]
  |_ -> raise ParsingData.InternalLexingError;;

(* handle character escapes and numerals *)
let resolve_literal lit_str =
  let lit_switch = Str.regexp "[\\]x\\|[\\]0\\|[\\]c\\|[\\].\\|." in
  let _ = if not (Str.string_match lit_switch lit_str 0) then
            raise ParsingData.InternalLexingError in
  let lit_head = Str.matched_string lit_str in
  match lit_head with
    "\\x" -> 
      let code = int_of_string (Str.replace_first lit_switch "0x" lit_str) in
      Char.chr code
    |"\\0" -> 
      let code = int_of_string (Str.replace_first lit_switch "0o" lit_str) in
      Char.chr code
    |"\\c" ->
      begin
        match lit_str.[2] with
          '?' -> '\x7f'|
          c -> Char.chr (Char.code c - Char.code '@')
      end
    |"\\t" -> '\t'
    |"\\n" -> '\n'
    |"\\r" -> '\r'
    |"\\f" -> '\x0c'
    |"\\a" -> '\x07'
    |"\\e" -> '\x1b'
    |_ -> lit_str.[0];;

(* map of modifiers *)
let flg_map = Hashtbl.create 8;;
Hashtbl.add flg_map 'd' ParsingData.flg_unix_lines;;
Hashtbl.add flg_map 'i' ParsingData.flg_no_case;;
Hashtbl.add flg_map 'm' ParsingData.flg_multiline;;
Hashtbl.add flg_map 's' ParsingData.flg_dotall;;

(* resolve modifier *)
let get_flag c cpos =
  try
    Hashtbl.find flg_map c
  with Not_found ->
    raise (ParsingData.UnsupportedInlineModifier(cpos, c));;

(* functions for querying token position *)
let get_pos lbuf = (Lexing.lexeme_start lbuf, Lexing.lexeme_end lbuf - 1);;
let get_spos lbuf = Lexing.lexeme_start lbuf;;
let get_epos lbuf = Lexing.lexeme_end lbuf - 1;;
}

let escape_char = '\\'

let hex_literal = escape_char 'x' ['0' - '9' 'a' - 'f' 'A' - 'F'] ['0' - '9' 'a' - 'f' 'A' - 'F']
let oct_literal = escape_char '0' (['0' - '7'] | ['0' - '7']['0' - '7'] | ['0' - '3']['0' - '7']['0' - '7'])
let ctrl_literal = escape_char 'c' ['?' '@' - '_']
let nmd_literal = escape_char ['t' 'n' 'r' 'f' 'a' 'e']

let encoded_literals = hex_literal | oct_literal | ctrl_literal | nmd_literal

let normal_literal = encoded_literals | [^'\\']
let chead_literal = encoded_literals | [^'[' '\\']
let cbody_literal = encoded_literals | [^'[' ']' '\\']

let plain_chead_u = [^'[' '\n' '\\']
let plain_chead_v = [^'[' ']' '\n' '\\']
let plain_cbody_u = [^'[' ']' '\n' '\\']
let plain_cbody_v = [^'[' ']' '\n' '\\']

let range_chead_u = encoded_literals | plain_chead_u as u
let range_chead_v = encoded_literals | plain_chead_v as v
let range_cbody_u = encoded_literals | plain_cbody_u as u 
let range_cbody_v = encoded_literals | plain_cbody_v as v

let range_chead = range_chead_u '-' range_chead_v 
let range_cbody = range_cbody_u '-' range_cbody_v

let posix_names = "Lower" | "Upper" | "ASCII" | "Alpha" | "Digit" | "Alnum" | "Punct" | "Graph" | "Print" | "Blank" | "Cntrl" | "XDigit" | "Space"
let predefined_cls = escape_char (['d' 'D' 's' 'S' 'w' 'W'] | 'p' '{' posix_names '}')

rule tk_normal = 
  parse '\n' { Eos }
    |'|' { VBar }
    |'*''+' { raise (ParsingData.UnsupportedPossessiveQuantifier(get_epos lexbuf)) }
    |'*''?' { Repetition(get_epos lexbuf, (0, -1, ParsingData.Rq)) }
    |'*' { Repetition(get_epos lexbuf, (0, -1, ParsingData.Gq)) }
    |'+''+' { raise (ParsingData.UnsupportedPossessiveQuantifier(get_epos lexbuf)) }
    |'+''?' { Repetition(get_epos lexbuf, (1, -1, ParsingData.Rq)) }
    |'+' { Repetition(get_epos lexbuf, (1, -1, ParsingData.Gq)) }
    |'?''+' { raise (ParsingData.UnsupportedPossessiveQuantifier(get_epos lexbuf)) }
    |'?''?' { Repetition(get_epos lexbuf, (0, 1, ParsingData.Rq)) }
    |'?' { Repetition(get_epos lexbuf, (0, 1, ParsingData.Gq)) }
    |'{' (['0' - '9']+) '}' '+' { raise (ParsingData.UnsupportedPossessiveQuantifier(get_epos lexbuf)) }
    |'{' (['0' - '9']+ as m_str) '}' '?' { let m = int_of_string m_str in Repetition(get_epos lexbuf, (m, m, ParsingData.Rq)) }
    |'{' (['0' - '9']+ as m_str) '}' { let m = int_of_string m_str in Repetition(get_epos lexbuf, (m, m, ParsingData.Gq)) }
    |'{' (['0' - '9']+) ',' '}' '+' { raise (ParsingData.UnsupportedPossessiveQuantifier(get_epos lexbuf)) }
    |'{' (['0' - '9']+ as m_str) ',' '}' '?' { let m = int_of_string m_str in Repetition(get_epos lexbuf, (m, -1, ParsingData.Rq)) }
    |'{' (['0' - '9']+ as m_str) ',' '}' { let m = int_of_string m_str in Repetition(get_epos lexbuf, (m, -1, ParsingData.Gq)) }
    |'{' (['0' - '9']+) ',' (['0' - '9']+) '}' '+' { raise (ParsingData.UnsupportedPossessiveQuantifier(get_epos lexbuf)) }
    |'{' (['0' - '9']+ as m_str) ',' (['0' - '9']+ as n_str) '}' '?' { Repetition(get_epos lexbuf, (int_of_string m_str, int_of_string n_str, ParsingData.Rq)) }
    |'{' (['0' - '9']+ as m_str) ',' (['0' - '9']+ as n_str) '}' { Repetition(get_epos lexbuf, (int_of_string m_str, int_of_string n_str, ParsingData.Gq)) }
    |'{' { raise (ParsingData.IncompleteRangeDefinition(get_spos lexbuf)) }
    |'(''?'':' { GrpOpen(get_spos lexbuf, ParsingData.NOCAP) }
    |'(''?''=' { GrpOpen(get_spos lexbuf, ParsingData.PLA) }
    |'(''?''!' { GrpOpen(get_spos lexbuf, ParsingData.NLA) }
    |'(''?''<''=' { GrpOpen(get_spos lexbuf, ParsingData.PLB) }
    |'(''?''<''!' { GrpOpen(get_spos lexbuf, ParsingData.NLB) }
    |'(''?''>' { GrpOpen(get_spos lexbuf, ParsingData.ATOMIC) }
    |'(''?' { ModsGrpOpen(get_spos lexbuf) }
    |'(' { GrpOpen(get_spos lexbuf, ParsingData.CAP(0)) }
    |')' { GrpClose(get_spos lexbuf) }
    |'[''^' { ClsOpen(get_spos lexbuf, true) }
    |'[' { ClsOpen(get_spos lexbuf, false) }
    |'^' { Anchor(get_pos lexbuf, ParsingData.Bol) }
    |'$' { Anchor(get_pos lexbuf, ParsingData.Eol) }
    |'.' { TkDot(get_spos lexbuf) }
    |'\\''b' { Anchor(get_pos lexbuf, ParsingData.Wordb) }
    |'\\''B' { Anchor(get_pos lexbuf, ParsingData.NWordb) }
    |'\\''A' { Anchor(get_pos lexbuf, ParsingData.Boi) }
    |'\\''G' { Anchor(get_pos lexbuf, ParsingData.Eom) }
    |'\\''Z' { Anchor(get_pos lexbuf, ParsingData.Eoi1) }
    |'\\''z' { Anchor(get_pos lexbuf, ParsingData.Eoi2) }
    |'\\''Q' { BeginQuote(get_pos lexbuf) }
    |'\\' (['1' - '9']['0' - '9'] * as num) { TkBackref(get_pos lexbuf, int_of_string num) }
    |normal_literal as u { Literal(get_pos lexbuf, resolve_literal u) }
    |predefined_cls as cls { ClsNamed(get_pos lexbuf, resolve_class cls) }
    |'\\'(['a' - 'z' 'A' - 'Z' '\n'] as c) { raise (ParsingData.UnsupportedEscape(get_epos lexbuf, c)) }
    |'\\' (_ as c) { Literal(get_pos lexbuf, c) } 
    |eof { raise ParsingData.UnexpectedEndOfInput }
and tk_class_header =
  parse '\n' { Eos }
    |range_chead { ClsRange(resolve_literal u, resolve_literal v) }
    |chead_literal as u { Literal(get_pos lexbuf, resolve_literal u) }
    |predefined_cls as cls { ClsNamed(get_pos lexbuf, resolve_class cls) }
    |'\\'(['1' - '9' 'a' - 'z' 'A' - 'Z' '\n'] as c) { raise (ParsingData.UnsupportedEscape(get_epos lexbuf, c)) }
    |'\\' (_ as c) { Literal(get_pos lexbuf, c) } 
    |eof { raise ParsingData.UnexpectedEndOfInput }
and tk_class_body =
  parse '\n' { Eos }
    |range_cbody { ClsRange(resolve_literal u, resolve_literal v) }
    |cbody_literal as u { Literal(get_pos lexbuf, resolve_literal u) }
    |predefined_cls as cls { ClsNamed(get_pos lexbuf, resolve_class cls) }
    |'\\'(['1' - '9' 'a' - 'z' 'A' - 'Z' '\n'] as c) { raise (ParsingData.UnsupportedEscape(get_epos lexbuf, c)) }
    |'\\' (_ as c) { Literal(get_pos lexbuf, c) } 
    |'\x5d' { ClsClose(get_spos lexbuf) } 
    |eof { raise ParsingData.UnexpectedEndOfInput }
and tk_mods_head =
  parse '\n' { Eos }
    |':' { EndMods }
    |'-' { NegMods }
    |')' { GrpClose(get_spos lexbuf) }
    | _ as c { Mod(get_flag c (get_spos lexbuf)) }
    |eof { raise ParsingData.UnexpectedEndOfInput }
and tk_quote =
  parse '\n' { Eos }
    |'\\''E' { EndQuote(get_pos lexbuf) }
    |_ as u { Literal(get_pos lexbuf, u) }
    |eof { raise ParsingData.UnexpectedEndOfInput }
