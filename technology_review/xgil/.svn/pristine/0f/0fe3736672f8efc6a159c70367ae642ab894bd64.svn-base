(* lexer.mll *)
(* based on an example from camllex documentation *)

{
  (* this encodes both the token kind (the constructor name) and
   * its lexeme (the constructor arguments);
   * unlike lex, ocamllex does not separate the concepts
   *)
  type tToken =
    | EOF
    | INT of int        (* integer literal *)
    | PLUS
    | MINUS
    | TIMES
    | DIV
    | LPAREN
    | RPAREN

  (* The following functions should probably be implemented by
   * some automatic translator, given the definition of tToken.
   * ocamlyacc does this (to some degree), but Elkhound does not.
   *)

  (* break out the token kind as an integer *)
  let tokenKind (t:tToken) : int =
  begin
    match t with
    | EOF ->     0
    | INT(_) ->  1
    | PLUS ->    2
    | MINUS ->   3
    | TIMES ->   4
    | DIV ->     5
    | LPAREN ->  6
    | RPAREN ->  7
  end

  (* render a token kind code as a string *)
  let tokenKindDesc (t:int) : string =
  begin
    match t with
    | 0 ->       "EOF"
    | 1 ->       "INT"
    | 2 ->       "+"
    | 3 ->       "-"
    | 4 ->       "*"
    | 5 ->       "/"
    | 6 ->       "("
    | 7 ->       ")"
    | _ ->       (failwith "bad token kind")
  end

  (* render a full tToken as a string *)
  let tokenDesc (t:tToken) : string =
  begin
    match t with
    | INT(i) ->  "INT(" ^ (string_of_int i) ^ ")"
    | _ ->       (tokenKindDesc (tokenKind t))
  end
}

rule readToken = parse
    [' ' '\t' '\n']     { readToken lexbuf }     (* skip whitespace *)
  | ['0'-'9']+          { INT(int_of_string(Lexing.lexeme lexbuf)) }
  | '+'                 { PLUS }
  | '-'                 { MINUS }
  | '*'                 { TIMES }
  | '/'                 { DIV }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | eof                 { EOF }
