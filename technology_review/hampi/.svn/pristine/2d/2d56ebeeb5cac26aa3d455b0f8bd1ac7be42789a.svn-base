lexer grammar Hampi;

@header { 
     package hampi.parser; 
   }

T__70 : '..' ;

// $ANTLR src "src/hampi/parser/Hampi.g" 117
KW_VAR : 'var' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 118
KW_CONCAT : 'concat';
// $ANTLR src "src/hampi/parser/Hampi.g" 119
KW_CFG : 'cfg' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 120
KW_VAL : 'val' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 121
KW_REG : 'reg' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 122
KW_QUERY: 'query';
// $ANTLR src "src/hampi/parser/Hampi.g" 123
KW_FIX : 'fix' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 124
KW_ASSERT : 'assert' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 125
KW_CONTAINS : 'contains' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 126
KW_IN : 'in' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 127
KW_STAR : 'star' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 128
KW_OR : 'or' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 129
KW_NOT : 'not' ;
// $ANTLR src "src/hampi/parser/Hampi.g" 130
KW_EQUALS : 'equals';


// Punctuation
// $ANTLR src "src/hampi/parser/Hampi.g" 134
LPAREN : '(';
// $ANTLR src "src/hampi/parser/Hampi.g" 135
RPAREN : ')';
// $ANTLR src "src/hampi/parser/Hampi.g" 136
LSQUARE : '[';
// $ANTLR src "src/hampi/parser/Hampi.g" 137
RSQUARE : ']';
// $ANTLR src "src/hampi/parser/Hampi.g" 138
COMMA : ',';	
// $ANTLR src "src/hampi/parser/Hampi.g" 139
EQUALS : '=';
// $ANTLR src "src/hampi/parser/Hampi.g" 140
NOTEQUALS : '!=';
// $ANTLR src "src/hampi/parser/Hampi.g" 141
ASSIGN : ':=';
// $ANTLR src "src/hampi/parser/Hampi.g" 142
SEMI : ';';
// $ANTLR src "src/hampi/parser/Hampi.g" 143
COLON : ':';
// $ANTLR src "src/hampi/parser/Hampi.g" 144
STAR: '*'; 
// $ANTLR src "src/hampi/parser/Hampi.g" 145
PLUS: '+'; 
// $ANTLR src "src/hampi/parser/Hampi.g" 146
BAR: '|'; 
// $ANTLR src "src/hampi/parser/Hampi.g" 147
MINUS : '-';
// $ANTLR src "src/hampi/parser/Hampi.g" 148
QUESTION: '?'; 

// $ANTLR src "src/hampi/parser/Hampi.g" 150
INT : ('0'..'9')+;

// $ANTLR src "src/hampi/parser/Hampi.g" 152
ID : ('a'..'z'|'A'..'Z'|'_'|'.'|'0'..'9')+ | '\`' ('a'..'z'|'A'..'Z'|'_'|'.'|'0'..'9')+ '\`'; 

// $ANTLR src "src/hampi/parser/Hampi.g" 154
STR_LIT : '\"' ( EscapeSequence | ~('\"'|'\\'))* '\"' ;

// $ANTLR src "src/hampi/parser/Hampi.g" 156
CHAR_SEQ : '\\' ('0'..'9')('0'..'9')('0'..'9') ; // PIETER

// $ANTLR src "src/hampi/parser/Hampi.g" 158
CHAR_LIT : '\'' ( EscapeSequence | ~('\"'|'\\')) '\''; 

// $ANTLR src "src/hampi/parser/Hampi.g" 160
fragment
EscapeSequence
    :   '\\' ('b'|'t'|'n'|'f'|'r'|'\"'|'\''|'\\')
    ;

// $ANTLR src "src/hampi/parser/Hampi.g" 165
NEWLINE
    :	'\r'? '\n' { skip(); }
    ;

// $ANTLR src "src/hampi/parser/Hampi.g" 169
WS  :   (' '|'\t')+ { skip(); }
    ;
   
// $ANTLR src "src/hampi/parser/Hampi.g" 172
COMMENT
    :   '/*' ( options {greedy=false;} : . )* '*/' {skip();}
    ;

// $ANTLR src "src/hampi/parser/Hampi.g" 176
LINE_COMMENT
    : '//'  ~('\n'|'\r')* '\r'? '\n' {skip();}
    ;
