(* File lexer.mll *)

{
open Parser        (* The type token is defined in parser.mli *)
}

rule token = parse
    [' ' '\t' '\n' '\r']                                     { token lexbuf }
  | "/*" ([^ '*']* | ([^ '*']* '*' [^ '/'])*) "*/"           { token lexbuf }
  | ':'                                                      { Colon }
  | ';'                                                      { Semicolon }
  | eof                                                      { EOF }
  | '"'((_ # '"')* as terminal)'"'                           { Terminal(terminal) }
  | '['(_ # ']')*']'                                         { Name }
  | (_ # [' ' '\t' '\n' ';' ':' '"' '[' ']' '\r'])* as s     { String(s) }

