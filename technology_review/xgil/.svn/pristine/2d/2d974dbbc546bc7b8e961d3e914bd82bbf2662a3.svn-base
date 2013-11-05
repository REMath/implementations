/* oc_arith.mly */
/* arith grammar, ocamlyacc syntax */

%token EOF
%token <int> TOK_NUMBER
%token TOK_PLUS
%token TOK_MINUS
%token TOK_TIMES
%token TOK_DIVIDE
%token TOK_LPAREN
%token TOK_RPAREN

/* low precedence */
%left TOK_PLUS TOK_MINUS
%left TOK_TIMES TOK_DIVIDE
/* high precedence */

%start main
%type <int> main
%type <int> exp
%type <int> parenthesizedExp

%%

main:
    exp EOF                    { $1 }
;

exp:
    exp TOK_PLUS exp           { $1 + $3 }
  | exp TOK_MINUS exp          { $1 - $3 }
  | exp TOK_TIMES exp          { $1 * $3 }
  | exp TOK_DIVIDE exp         { $1 / $3 }
  | TOK_NUMBER                 { $1 }
  | parenthesizedExp           { $1 }
;

parenthesizedExp:
    TOK_LPAREN exp TOK_RPAREN  { $2 }
;

/* EOF */
