%{
  
  let token_var = ref 0
  let token_pp = ref 0

  let find var_tab s = 
    try Hashtbl.find var_tab s 
    with Not_found -> 
      Hashtbl.add var_tab s !token_var;
      let p = !token_var in
	incr token_var;
	p
	  
  let new_pp () = 
    let p = !token_pp in
      incr token_pp;
      p

  let vars_used var_tab = Hashtbl.fold (fun s p l -> p::l) var_tab []
			    
%}

%token FOR ASSERT ENSURE SKIP WHILE IF ELSE NOT AND OR EOF LP RP LB RB EQ NEQ LE LT GE GT PVL VL PT PTPT ASSIGN UNKNOWN ADD SUB MULT
%token <string> IDENT
%token <int> INT

%left AND OR
%left SUB ADD
%left MULT
%nonassoc NOT

%start prog
%type < Syntax.program > prog

%%

prog:
 | instrs EOF { $1, new_pp() }
;
  
option_pvl : 
 | PVL {}
 |     {}


instrs : 
  | instr option_pvl { $1 }
  | instr PVL instrs { Syntax.Seq ($1,$3) }
  | LB instrs RB {$2 }

expr:
 | INT            { Syntax.Const $1 }
 | LP expr RP     { $2 }
 | UNKNOWN        { Syntax.Unknown }
 | IDENT          { Syntax.Var $1}
 | SUB expr       { Syntax.Binop (Syntax.Sub,Syntax.Const 0,$2) }
 | expr ADD expr  { Syntax.Binop (Syntax.Add,$1,$3) }
 | expr SUB expr  { Syntax.Binop (Syntax.Sub,$1,$3) }
 | expr MULT expr { Syntax.Binop (Syntax.Mult,$1,$3) }
;


test:
 | LP test RP     { $2 }
 | expr comp expr { Syntax.Comp ($2,$1,$3) }
 | test AND test  { Syntax.And ($1,$3) }
 | test OR test   { Syntax.Or ($1,$3) }
;

comp:
 | ASSIGN { Syntax.Eq }
 | EQ  { Syntax.Eq }
 | NEQ { Syntax.Neq }
 | LE  { Syntax.Le }
 | LT  { Syntax.Lt }

instr:
 | IDENT ASSIGN expr        { Syntax.Assign (new_pp (),$1,$3) }
 | SKIP                     { Syntax.Skip (new_pp ())}
/* | ASSERT test            { Syntax.Assert ($2 var_tab) } 
 | ENSURE test              { Syntax.Ensure ($2 var_tab) } */
 | IF test block ELSE block { Syntax.If (new_pp (),$2,$3,$5) }
/* | IF test block            { Syntax.If ($2,$3,Syntax.Skip) } */
 | WHILE test  block        { Syntax.While (new_pp (),$2,$3) }
 | FOR LP IDENT ASSIGN expr PVL test PVL expr RP block
      {
	let init = Syntax.Assign (new_pp (),$3, $5) in
	let incr = Syntax.Assign (new_pp (),$3, $9) in	  
	let body = Syntax.While(new_pp (),$7,Syntax.Seq (incr,$11)) in	  
	  Syntax.Seq (init,body)
      } 
;

block:
	| instr        { $1 }
	| LB instrs RB { $2 }
	| LB RB        { Syntax.Skip (new_pp ())}
;
%%

