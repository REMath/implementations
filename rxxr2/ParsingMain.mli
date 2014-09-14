(* © Copyright University of Birmingham, UK *)

open ParsingData

(* main method for parsing a pattern of the form [/]REGEX[/MODS] *)
val parse_pattern : Lexing.lexbuf -> pattern;;
