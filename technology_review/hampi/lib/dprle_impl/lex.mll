{
(*  Copyright (c) 2008, University of Virginia
    All rights reserved.
   
    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:
       * Redistributions of source code must retain the above copyright
         notice, this list of conditions and the following disclaimer.
       * Redistributions in binary form must reproduce the above
         copyright notice, this list of conditions and the following
         disclaimer in the documentation and/or other materials
         provided with the distribution.
       * Neither the name of the University of Virginia  nor the names 
         of its contributors may be used to endorse or promote products
         derived from this software without specific prior written
         permission.
   
    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
    (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
    SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
    HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
    STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
    ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
    OF THE POSSIBILITY OF SUCH DAMAGE.
   
    Author: Pieter Hooimeijer
*)
  open Parse
  open Printf

  let pp_token token = match token with
    | LBRACKET          -> Printf.printf "["
    | RBRACKET          -> Printf.printf "]"
    | LBRACE            -> Printf.printf "{"
    | RBRACE            -> Printf.printf "}"
    | LPAREN            -> Printf.printf "("
    | RPAREN            -> Printf.printf ")"
    | COMMA             -> Printf.printf ", "
    | ARROW             -> Printf.printf "->"
    | IDENT s           -> Printf.printf "IDENT(%s)" s
    | SYMBOL s          -> Printf.printf "SYMBOL(%s)" s
    | PUSH              -> Printf.printf "PUSH"
    | POP               -> Printf.printf "POP"
    | ON                -> Printf.printf "ON"
    | ANY               -> Printf.printf "ANY"
    | OUTPUT            -> Printf.printf "OUTPUT"
    | CONCAT            -> Printf.printf "CONCAT"
    | EPSILON           -> Printf.printf "EPSILON"
    | SUBSET            -> Printf.printf "subset"
    | QUOTE             -> Printf.printf "'"
    | START             -> Printf.printf "s:"
    | FINAL             -> Printf.printf "f:"
    | DELTA             -> Printf.printf "d:"
    | SOLVE             -> Printf.printf "SOLVE"
    | SEMICOLON         -> Printf.printf ";"
    | UNKNOWN           -> Printf.printf "[LEX ERROR]"

  let keywords =
    let table = Hashtbl.create 10 in
    let keywordlist = [ ("push"  , PUSH);
			("pop"   , POP);
			("on"    , ON);
			("any"   , ANY);
			("output", OUTPUT);
			("concat", CONCAT);
			("solve" , SOLVE);
			("subset", SUBSET);
		        ("epsilon", EPSILON) ] in
    let _ = List.iter (fun (x,y) -> Hashtbl.replace table x y) keywordlist in
      table

  (* From the ocamllex documentation... *)
  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- 
	{ pos with
	    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
	    Lexing.pos_bol = pos.Lexing.pos_cnum;
	}
}

let ident = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9']*

  rule handletop = parse
    | '[' { LBRACKET }
    | ']' { RBRACKET }
    | '{' { LBRACE }
    | '}' { RBRACE }
    | '(' { LPAREN }
    | ')' { RPAREN }
    | ',' { COMMA }
    | '#' { handlecomment lexbuf } (* ignore comments *)
    | "->" { ARROW }
    | ";" { SEMICOLON }
    | ident as somestring { try 
			      Hashtbl.find keywords somestring
			    with Not_found ->
			      IDENT somestring }
    | "'" { let stringbuffer = Buffer.create 5 in
	       handlestring stringbuffer lexbuf }
    | "s:" { START }
    | "f:" { FINAL }
    | "d:" { DELTA }
    | [' ' '\t' ] { handletop lexbuf } (* ignore whitespace *)
    | '\n' | "\r\n" { incr_linenum lexbuf; handletop lexbuf }
    | eof { raise End_of_file }
    | _ { UNKNOWN }
  and handlestring buffer = parse
    | "\\'" { Buffer.add_char buffer '\'' ; handlestring buffer lexbuf }
    | "'" { SYMBOL (Buffer.contents buffer) }
    | ['\n' '\r'] { Printf.printf "Lexing error: unterminated string token on line %d\n"
		    lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum ; exit(1) }
    | _ as c { Buffer.add_char buffer c ; handlestring buffer lexbuf}
  and handlecomment = parse
    | '\n' | "\r\n" { incr_linenum lexbuf; handletop lexbuf }
    | eof { raise End_of_file }
    | _ { handlecomment lexbuf }
