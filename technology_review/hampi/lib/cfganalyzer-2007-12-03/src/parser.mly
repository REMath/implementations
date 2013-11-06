/* File parser.mly */
%{

open Cfg

%}

%token Colon, Semicolon, Quotes
%token Name
%token <string> String
%token <string> Terminal
%token EOF

%start cfg
%type <Cfg.pureCFG> cfg
%%

cfg:
    EOF                                         { [] }
  | vardecl cfg                                 { $1 :: $2 }
;
 
vardecl:
    nonterminal rules                           { ($1,$2) }
;

nonterminal:
    String                                      { $1 }
;

rules:
    rule                                        { [ $1 ] }
  | rule rules                                  { $1 :: $2 }
;

rule:
    rulename Colon symbollist Semicolon         { $3 }
;

rulename:
    Name                                        { () }
  |                                             { () }
;

symbollist:
    symbol symbollist                           { $1 :: $2 }
  |                                             { [] }
;

symbol:
    String                                      { Nonterminal($1) }
  | Terminal                                    { Terminal($1) }
;


%%




