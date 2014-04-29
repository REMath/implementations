%{

  open Goto
  open AbMachineNonrel
  open Camlcoq

  let labelmap = Hashtbl.create 17
  let appendlabel = Hashtbl.add labelmap
  let getlabel = Hashtbl.find labelmap

%}

%token <int> INT
%token <Goto.register> REGISTER
%token <string> LABEL
%token <int> COLON
%token ARROW
%token STAR
%token COMMA
%token LPAREN
%token RPAREN
%token PLUS
%token GE
%token CST
%token ENC
%token ADD
%token SUB
%token MUL
%token CMP
%token SKIP
%token HALT
%token GOTO
%token GOTOLE
%token GOTOLT
%token GOTOEQ
%token LOAD
%token STORE
%token NL
%token EOF

%left PLUS

%start prog
%type <Goto.instruction list> prog
%type <((string -> Camlcoq.Z.t) -> Goto.instruction) * bool> instr

%%

prog: instr_list EOF { Reloc.reloc getlabel $1 }
;

instr_list:
| /* empty */          { [] }
| instr NL instr_list  { $1 :: $3 }
;

instr:
| /* empty */             {(fun _ -> ISkip), false}
| CST num ARROW REGISTER  {(fun f -> ICst($2 f, $4)), true}
| ADD REGISTER ARROW REGISTER {(fun _ -> IBinop(OpAdd, $2,$4)), false}
| SUB REGISTER ARROW REGISTER {(fun _ -> IBinop(OpSub, $2,$4)), false}
| MUL REGISTER ARROW REGISTER {(fun _ -> IBinop(OpMul, $2,$4)), false}
| CMP REGISTER REGISTER   {(fun _ -> ICmp($2,$3)), false}
| CMP REGISTER COMMA REGISTER   {(fun _ -> ICmp($2,$4)), false}
| CMP REGISTER GE REGISTER{(fun _ -> ICmp($2,$4)), false}
| SKIP                    {(fun _ -> ISkip), false}
| HALT REGISTER           {(fun _ -> IHalt $2), false}
| GOTO num                {(fun f -> IGoto ($2 f)), true}
| GOTOLE num              {(fun f -> IGotoCond (FLE, $2 f)), true}
| GOTOLT num              {(fun f -> IGotoCond (FLT, $2 f)), true}
| GOTOEQ num              {(fun f -> IGotoCond (FEQ, $2 f)), true}
| GOTO REGISTER           {(fun _ -> IGotoInd $2), false}
| GOTO STAR REGISTER      {(fun _ -> IGotoInd $3), false}
| LOAD STAR REGISTER ARROW REGISTER  {(fun _ -> ILoad($3,$5)), false}
| STORE REGISTER ARROW STAR REGISTER {(fun _ -> IStore($2,$5)), false}
| LABEL COLON instr       { appendlabel $1 $2; $3}
| LPAREN instr RPAREN     { $2 }
;

num:
| INT               { fun _ -> Integers.Int.repr (Z.of_sint $1) }
| LABEL             { fun f -> f $1 }
| num PLUS num      { fun f -> Integers.Int.add ($1 f) ($3 f) }
| LPAREN num RPAREN { fun f -> $2 f }
| ENC LPAREN instr RPAREN { fun f -> let i = (fst $3) f in
                                     match encode_instr i with
                                     | n :: nil -> n
                                     | _ -> failwith (Printf.sprintf "Encoded %s should be exactly one byte" (Utils.string_of_instr i)) }
;

