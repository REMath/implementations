%{
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
  open Lexing
  open Depgraph 
  
  let tempcount = ref 0

  let new_temp () = 
    incr tempcount ;
    "_t" ^ string_of_int(!tempcount)

  let parse_error s =
    flush stdout

  let curnfa : (Nfa.nfa option) ref = ref None
    
%}

%token LBRACKET RBRACKET LBRACE RBRACE LPAREN RPAREN COMMA ARROW QUOTE SUBSET SEMICOLON
%token <string> IDENT SYMBOL
%token PUSH POP SOLVE ON ANY OUTPUT CONCAT EPSILON START FINAL DELTA UNKNOWN

%start statement
%type <unit> statement

%%
statement: error {
               let startpos = Parsing.rhs_start_pos 2 in
	       let endpos  = Parsing.rhs_end_pos 2 in
                 Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected subset constraint or command.\n"
	           startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		   endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)	   
             }
           | expr error {
	       let startpos = Parsing.rhs_start_pos 2 in
	       let endpos  = Parsing.rhs_end_pos 2 in
                 Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected 'subset.'\n"
	           startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		   endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)	   
	     }
           | expr SUBSET error {
	       let startpos = Parsing.rhs_start_pos 3 in
	       let endpos  = Parsing.rhs_end_pos 3 in
                 Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected identifier or machine definition.\n"
	           startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		   endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)	   
	     }
           | expr SUBSET rhs error {
	       let startpos = Parsing.rhs_start_pos 4 in
	       let endpos  = Parsing.rhs_end_pos 4 in
                 Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected ';.'\n"
	           startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		   endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)	   
	     }

           | expr SUBSET rhs SEMICOLON { 
	       let varname, is_nfa = $3 in
		   Depgraph.add_isect (Depgraph.cur_graph ()) varname $1
	     }
	   | command error {
	       let startpos = Parsing.rhs_start_pos 2 in
	       let endpos  = Parsing.rhs_end_pos 2 in
                 Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected ';.'\n"
	           startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		   endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)	   
	     }
           | command SEMICOLON { }

rhs:      IDENT {
               ($1, false)
           }

           | machinedef     { 
	       let varname = new_temp () in 
	       let _ = Depgraph.new_node (Depgraph.cur_graph ()) varname (Some $1) in
		 (varname, true)
	     }

	     
expr:    IDENT { let _ = Depgraph.find_node (Depgraph.cur_graph ()) $1 in
		   $1
	       }
	   | CONCAT error {
	       let startpos = Parsing.rhs_start_pos 2 in
	       let endpos  = Parsing.rhs_end_pos 2 in
                 Printf.printf "\n# Parse error (%d.%d-%d.%d): 'Concat' takes two expression parameters.\n"
	           startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		   endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)	   
	     }
           | CONCAT LPAREN expr COMMA expr RPAREN { 
               let varname = new_temp () in
               let _ = Depgraph.new_node (Depgraph.cur_graph ()) varname None in
               let _ = Depgraph.add_concat (Depgraph.cur_graph ()) $3 $5 varname in
                 varname
	     }
	     

machinedef: LBRACKET error {
	       let startpos = Parsing.rhs_start_pos 2 in
	       let endpos  = Parsing.rhs_end_pos 2 in
                 Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected 's:.'\n"
	           startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		   endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
	     }
	   | LBRACKET START error {
              let startpos = Parsing.rhs_start_pos 3 in
	       let endpos  = Parsing.rhs_end_pos 3 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected identifier.\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)  
            }
	   | LBRACKET START IDENT error {
              let startpos = Parsing.rhs_start_pos 4 in
	       let endpos  = Parsing.rhs_end_pos 4 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected 'f:.'\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
	     }
	   | LBRACKET START IDENT FINAL error {
              let startpos = Parsing.rhs_start_pos 5 in
	       let endpos  = Parsing.rhs_end_pos 5 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected identifier.\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
	     }
	   | LBRACKET START IDENT FINAL IDENT error {
	       let startpos = Parsing.rhs_start_pos 6 in
	       let endpos  = Parsing.rhs_end_pos 6 in
                 Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected 'd:.'\n"
	           startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		   endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
	     }
	   | LBRACKET START IDENT FINAL IDENT DELTA transitionlist RBRACKET { 
	       let newnfa = match !curnfa with 
                 | None -> Nfa.new_nfa_states (Nfa.Base $3) (Nfa.Base $5)
                 | Some nfa -> Nfa.nfa_rename_states nfa (Nfa.Base $3) (Nfa.Base $5) in
		 curnfa := None;
		 newnfa
	     }

transitionlist: /* empty */ { }
           | transitionlist transition { }

transition: error {
              let startpos = Parsing.rhs_start_pos 1 in
	       let endpos  = Parsing.rhs_end_pos 1 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected ']' or transition of the form 'IDENT -> IDENT on { SYMBOLS }.'\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
  
} 
	   | IDENT error {
              let startpos = Parsing.rhs_start_pos 2 in
	       let endpos  = Parsing.rhs_end_pos 2 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected '->.'\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
}
	  | IDENT ARROW error {
              let startpos = Parsing.rhs_start_pos 3 in
	       let endpos  = Parsing.rhs_end_pos 3 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected identifier.\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
}
	  | IDENT ARROW IDENT error {
              let startpos = Parsing.rhs_start_pos 4 in
	       let endpos  = Parsing.rhs_end_pos 4 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected 'on.'\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
}
          | IDENT ARROW IDENT ON ANY { 
                                    let nfa = match !curnfa with 
				      | None ->
					  let newnfa = Nfa.new_nfa () in
					    curnfa := (Some newnfa); newnfa
				      | Some nfa -> nfa in
				      Nfa.add_all_trans nfa (Nfa.Base $1) (Nfa.Base $3)
}

          | IDENT ARROW IDENT ON symbolset { 
                                    let nfa = match !curnfa with 
				      | None ->
					  let newnfa = Nfa.new_nfa () in
					    curnfa := (Some newnfa); newnfa
				      | Some nfa -> nfa in
				      List.iter (fun x -> Nfa.add_trans nfa (Nfa.Base $1) x (Nfa.Base $3)) $5
}

symbolset: error { 
               let startpos = Parsing.rhs_start_pos 0 in
	       let endpos  = Parsing.rhs_end_pos 0 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected {}-delimited set of transition symbols.\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
}
	  | LBRACE RBRACE { [] }
          | LBRACE symbollist RBRACE { $2  }
          | LBRACE symbollist COMMA RBRACE { $2 }

symbollist: symbol { [ $1 ] }
          | symbollist error {
               let startpos = Parsing.rhs_start_pos 1 in
	       let endpos  = Parsing.rhs_end_pos 1 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Expected comma followed by transition symbols.\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)	      
	    }
	   | symbollist COMMA symbol { $3 :: $1 }

symbol : error {
               let startpos = Parsing.rhs_start_pos 1 in
	       let endpos  = Parsing.rhs_end_pos 1 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Unrecognized symbol (perhaps a missing single quote somewhere?).\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
         }
         | SYMBOL { Nfa.Character $1 }
	 | EPSILON { Nfa.Epsilon }

command:     IDENT LPAREN identoption RPAREN {
               let startpos = Parsing.rhs_start_pos 1 in
	       let endpos  = Parsing.rhs_end_pos 1 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): Unrecognized command.\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
             }
           | PUSH LPAREN RPAREN     { Depgraph.push () }
	   | POP  LPAREN RPAREN     { try Depgraph.pop () with Pop ->
					let startpos = Parsing.rhs_start_pos 1 in
					let endpos  = Parsing.rhs_end_pos 3 in
					  Printf.printf "Error (%d.%d-%d): Too many calls to pop().\n"
					    startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol) 
					    (endpos.pos_cnum - endpos.pos_bol);
					  exit(1) }
           | SOLVE LPAREN RPAREN {
	       let startpos = Parsing.rhs_start_pos 1 in
	       let endpos  = Parsing.rhs_end_pos 3 in
	       Printf.printf "\n# Solve (%d.%d-%d.%d) - Progress: "
	       	 startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol) 
		 endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 Solve.solve (Depgraph.cur_graph ())
	     }
	   | OUTPUT LPAREN IDENT RPAREN { 
	       let node = Depgraph.find_node (Depgraph.cur_graph ()) $3 in
	       let lang = node.lang in
               let startpos = Parsing.rhs_start_pos 1 in
	       let endpos  = Parsing.rhs_end_pos 4 in
	       let _ = Printf.printf "\n# Output (%d.%d-%d.%d):\n" 
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol) in
	       let _ = match lang with 
		 | None -> Printf.printf "%s = " $3; Nfa.print_nfa (Nfa.new_sigmastar ())
		 | Some lang -> Printf.printf "%s = " $3;
		     Nfa.print_nfa lang in ()
		       
             }
	   | OUTPUT error {
               let startpos = Parsing.rhs_start_pos 2 in
	       let endpos  = Parsing.rhs_end_pos 2 in
                Printf.printf "\n# Parse error (%d.%d-%d.%d): 'Output' takes a single identifier parameter.\n"
	          startpos.pos_lnum (startpos.pos_cnum - startpos.pos_bol)
		  endpos.pos_lnum (endpos.pos_cnum - endpos.pos_bol);
		 exit(1)
	     }

identoption : /* empty */ { }
	    | IDENT { } 
            | IDENT COMMA IDENT { }
	    | error { }

    
