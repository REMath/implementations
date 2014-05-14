/* ############################## L E X E R ############################ */
grammar Hampi;

/* ############################## P A R S E R ############################ */

	options {
		output = AST; 	// Automatically build the AST while parsing
		backtrack=true;
	}

	tokens {
	    CFGPROD;
	    ASSIGN;
	    PROGRAM;
	    CFGOPTION;
	    CFGSTAR;
	    CFGPLUS;
	    TEQUALS;
	    TNOTEQUALS;
	    FIX;
	    CONTAINS;
	    IN;
	    ASSERT;
	    CONCAT;
	    SUBSEQUENCE;
	    VAR;
	    CFG;
	    REG;
	    VAL;
	    CONST;
	    RANGE;
        CHARSEQRANGE; // PIETER
	    OR;
	    NOTIN;
	    NOTCONTAINS;
	    CFGCHARRANGE;
        CFGCHARSEQRANGE; // PIETER
	    CFGPRODELEMSET;
		VALS;//separator
	}
   
   @header { 
     package hampi.parser; 
   }

@lexer::header { 
     package hampi.parser; 
   }
	
	program : (statement SEMI)+ -> ^(PROGRAM statement+);
	
	statement : vardeclStmt 
	          | cfgStmt
	          | regStmt
	          | valDeclStmt
	          | assertStmt
	          ;
	          
	vardeclStmt :   (KW_VAR ID COLON INT '..' INT) -> ^(VAR ID INT INT)
                 |  (KW_VAR ID COLON INT) -> ^(VAR ID INT)
                ;
	
	cfgStmt : (KW_CFG cfgProduction) -> ^(CFG cfgProduction);
	
	cfgProduction : (ID ASSIGN  cfgProductionSet ) -> ^(CFGPROD ID cfgProductionSet );
	
	cfgProductionSet : (cfgProductionElementSet (BAR cfgProductionElementSet)*) -> cfgProductionElementSet+;
	
	cfgProductionElementSet : (cfgProductionElement* ) -> ^(CFGPRODELEMSET cfgProductionElement*); 
	
	cfgProductionElement : cfgTerminal -> cfgTerminal
	                     | cfgNonterminal -> cfgNonterminal
	                     | LPAREN cfgNonterminal RPAREN QUESTION -> ^(CFGOPTION cfgNonterminal)
	                     | LPAREN cfgNonterminal RPAREN STAR     -> ^(CFGSTAR     cfgNonterminal)
	                     | LPAREN cfgNonterminal RPAREN PLUS	 -> ^(CFGPLUS     cfgNonterminal)
	                     | LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE -> ^(CFGCHARRANGE CHAR_LIT CHAR_LIT)
                         | LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE -> ^(CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ) // PIETER
	                     ;
	                     
    cfgTerminal : STR_LIT
                | CHAR_SEQ; // PIETER

    cfgNonterminal : ID;
    
    regStmt : (KW_REG ID ASSIGN regDefinition) -> ^(REG ID regDefinition);

    regDefinition : ID -> ID
                  | STR_LIT -> STR_LIT
                  | CHAR_SEQ -> CHAR_SEQ // PIETER
                  | (KW_FIX LPAREN ID COMMA INT RPAREN) -> ^(FIX ID INT)
                  | (KW_STAR LPAREN regDefinition RPAREN) -> ^(STAR regDefinition)
                  | (LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE) -> ^(RANGE CHAR_LIT CHAR_LIT)
                  | (LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE) -> ^(CHARSEQRANGE CHAR_SEQ CHAR_SEQ) // PIETER
                  | (KW_OR LPAREN regDefinition (COMMA regDefinition)* RPAREN) -> ^(OR regDefinition+)
                  | (KW_CONCAT LPAREN regDefinition (COMMA regDefinition)* RPAREN) -> ^(CONCAT regDefinition+)
                   ;
	
	valDeclStmt : (KW_VAL ID ASSIGN expr) -> ^(VAL ID expr);
	
	expr : STR_LIT -> STR_LIT
	     | ID      -> ID
	     | (KW_CONCAT LPAREN expr (COMMA expr)* RPAREN) -> ^(CONCAT expr+)
	     | ID LSQUARE INT COLON INT RSQUARE -> ^(SUBSEQUENCE ID INT INT);
	
	assertStmt : (KW_ASSERT boolExpr) -> ^(ASSERT boolExpr);

    boolExpr :
               (ID KW_IN ID) -> ^(IN ID ID)
             | (ID KW_CONTAINS STR_LIT) -> ^(CONTAINS ID STR_LIT)
             | (ID KW_NOT KW_IN ID)            -> ^(NOTIN ID ID)
             | (ID KW_NOT KW_CONTAINS STR_LIT) -> ^(NOTCONTAINS ID STR_LIT)
             | (ID KW_EQUALS ID) -> ^(TEQUALS ID ID)
             | (ID KW_NOT KW_EQUALS ID) -> ^(TNOTEQUALS ID ID)
             ;
                 
//Keywords: case sensitive
KW_VAR : 'var' ;
KW_CONCAT : 'concat';
KW_CFG : 'cfg' ;
KW_VAL : 'val' ;
KW_REG : 'reg' ;
KW_QUERY: 'query';
KW_FIX : 'fix' ;
KW_ASSERT : 'assert' ;
KW_CONTAINS : 'contains' ;
KW_IN : 'in' ;
KW_STAR : 'star' ;
KW_OR : 'or' ;
KW_NOT : 'not' ;
KW_EQUALS : 'equals';


// Punctuation
LPAREN : '(';
RPAREN : ')';
LSQUARE : '[';
RSQUARE : ']';
COMMA : ',';	
EQUALS : '=';
NOTEQUALS : '!=';
ASSIGN : ':=';
SEMI : ';';
COLON : ':';
STAR: '*'; 
PLUS: '+'; 
BAR: '|'; 
MINUS : '-';
QUESTION: '?'; 

INT : ('0'..'9')+;

ID : ('a'..'z'|'A'..'Z'|'_'|'.'|'0'..'9')+ | '\`' ('a'..'z'|'A'..'Z'|'_'|'.'|'0'..'9')+ '\`'; 

STR_LIT : '\"' ( EscapeSequence | ~('\"'|'\\'))* '\"' ;

CHAR_SEQ : '\\' ('0'..'9')('0'..'9')('0'..'9') ; // PIETER

CHAR_LIT : '\'' ( EscapeSequence | ~('\"'|'\\')) '\''; 

fragment
EscapeSequence
    :   '\\' ('b'|'t'|'n'|'f'|'r'|'\"'|'\''|'\\')
    ;

NEWLINE
    :	'\r'? '\n' { skip(); }
    ;

WS  :   (' '|'\t')+ { skip(); }
    ;
   
COMMENT
    :   '/*' ( options {greedy=false;} : . )* '*/' {skip();}
    ;

LINE_COMMENT
    : '//'  ~('\n'|'\r')* '\r'? '\n' {skip();}
    ;
