(*
 *  This file is part of WhileAnalyser
 *  Copyright (c)2005-2008 INRIA Rennes - Bretagne Atlantique
 *  David Pichardie <first.last@irisa.fr>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

{
  open Lexing  (* il n'est ainsi pas necessaire de prefixer par "Lexing." 
                  la fonction lexeme *) 
  open While_parser  (* pour connaitre le type token *)

  exception Stop

  (*      table des mots clés     *)
  let kwd_tab = Hashtbl.create 23 

  let _ = (* initialisation de la table de hash *)
    Hashtbl.add kwd_tab "while" WHILE;
    Hashtbl.add kwd_tab "for" FOR;
    Hashtbl.add kwd_tab "skip" SKIP;
    Hashtbl.add kwd_tab "assert" ASSERT;
    Hashtbl.add kwd_tab "ensure" ENSURE;
    Hashtbl.add kwd_tab "if" IF;
    Hashtbl.add kwd_tab "else" ELSE;
    Hashtbl.add kwd_tab "not" NOT;
    Hashtbl.add kwd_tab "and" AND;
    Hashtbl.add kwd_tab "or" OR

  let id_or_kwd s = (* cherche le token associé à s ou renvoie IDENT s *)  
    try Hashtbl.find kwd_tab s 
    with Not_found -> IDENT(s) 

  (* pour gérer les commentaires imbriqués *)
  let level = ref 0

  let currentline = ref 1
}


let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = letter (letter | digit | '_' | '.')*
let integer = ['0'-'9']+
let float = integer '.' ['0'-'9']*
let space = [' ' '\t']

rule nexttoken = parse
    space+  { nexttoken lexbuf }
  | '\n'    { incr currentline; nexttoken lexbuf }
  | "(*"    { level := 1; comment lexbuf }
		| '#'[^'\n']*['\n'] {nexttoken  lexbuf}
(*  | "fin"   { raise Stop }*)
  | ident   { id_or_kwd (lexeme lexbuf) }
  | '{'     { LB }
  | '}'     { RB }
  | '('     { LP }
  | ')'     { RP }
  | "=="     { EQ }
  | "<>"    { NEQ }
  | "<="    { LE }
  | '<'     { LT }
  | ">="    { GE }
  | '>'     { GT }
  | ';'     { PVL }
  | '+'     { ADD }
  | '-'     { SUB }
  | '*'     { MULT }
  | '='     { ASSIGN }
  | ','     { VL }
  | '?'     { UNKNOWN }
  | '.'     { PT }
  | ':'     { PTPT }
  | "//"    { comment' lexbuf }
  | integer { INT (int_of_string (lexeme lexbuf)) }
  | eof     { EOF }

and comment = parse
  | "*)"    { level := !level - 1; 
              if !level = 0 then nexttoken lexbuf 
	      else comment lexbuf }
  | "(*"    { level := !level + 1; comment lexbuf }
  | _       { comment lexbuf }

and comment' = parse
  | '\n'    { incr currentline; nexttoken lexbuf }
  | _       { comment' lexbuf }

{
  (* pour faire des test sur le lexer *)
  let list_token file =
    if not (Sys.file_exists file) then
      failwith  ("le fichier "^file^" n'existe pas\n")
    else
      let buf = from_channel (open_in file) in
      let rec aux () =
	try
	  match (nexttoken buf) with
	      EOF -> []
	    | t -> t::(aux ())
	  with Failure _ -> 
	    print_string "aucun moyen de filtrer le token courant !"; []
      in aux ()

}
