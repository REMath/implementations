{

  open Lexing
  open Datatypes
  open Parser
  open Goto

  exception Lexical_error of string

  let id_or_keyword =
    let h = Hashtbl.create 17 in
    List.iter
     (fun (s,k) -> Hashtbl.add h s k)
      [
        "add", ADD;
        "sub", SUB;
        "mul", MUL;
        "cmp", CMP;
        "cst", CST;
        "enc", ENC;
        "goto", GOTO;
        "gotoLE", GOTOLE;
        "gotoLT", GOTOLT;
        "gotoEQ", GOTOEQ;
        (*"gotoInd", GOTOIND;*)
        "halt", HALT;
        "hlt", HALT;
        "ret", HALT;
        "return", HALT;
        "skip", SKIP;
        "store", STORE;
        "load", LOAD
      ];
    fun s -> 
      try Hashtbl.find h s with Not_found -> LABEL s

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let comment_cpt = ref 0
}

let alpha = ['a'-'z' 'A'-'Z' '_' '-' '.']
let digit = ['0'-'9']
let num = '-'? digit+
let ident = alpha (alpha | '\'' | digit)*

rule token = parse
  | '\n' { newline lexbuf ; NL}
  | [' ' '\t' '\r']+ 
      { token lexbuf }
  | "(*"   
      { incr comment_cpt; comment lexbuf; token lexbuf }
  | ":"
      { COLON ((-)lexbuf.lex_curr_p.pos_lnum 1)}
  | "\\geq" | ">=" { GE }
  | "R0" { REGISTER R0 }
  | "R1" { REGISTER R1 }
  | "R2" { REGISTER R2 }
  | "R3" { REGISTER R3 }
  | "R4" { REGISTER R4 }
  | "R5" { REGISTER R5 }
  | "R6" { REGISTER R6 }
  | "R7" { REGISTER R7 }
  | num
      { let i = lexeme lexbuf in
        try INT (int_of_string i)
        with Failure _ as e ->
          Printf.eprintf "Failure: int_of_string(%s)" i;
          raise e
      } 
  | ident 
      { id_or_keyword (lexeme lexbuf) }
  | "->" { ARROW }
  | "*" { STAR }
  | "+" { PLUS }
  | "," { COMMA }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | _ 
      { raise (Lexical_error (lexeme lexbuf)) }
  | eof
      { EOF }

and comment = parse
  | "(*" { incr comment_cpt; comment lexbuf }
  | "*)" { decr comment_cpt; if !comment_cpt > 0 then comment lexbuf }
  | "\n" { newline lexbuf; comment lexbuf }
  | _    { comment lexbuf }
  | eof  { raise (Lexical_error "unterminated comment") }

