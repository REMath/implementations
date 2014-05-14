(* lexer.mll *)
(* simple lexer for C++ *)

{
  open Parser
  exception Eof
}

rule token = parse
(* whitespace *)
  [' ' '\t' '\n']+                { token lexbuf }     (* skip ws *)

(* keywords, operators *)
| "asm"                           { TOK_ASM }
| "auto"                          { TOK_AUTO }
| "break"                         { TOK_BREAK }
| "bool"                          { TOK_BOOL }
| "case"                          { TOK_CASE }
| "catch"                         { TOK_CATCH }
| "cdecl"                         { TOK_CDECL }
| "char"                          { TOK_CHAR }
| "class"                         { TOK_CLASS }
| "const"                         { TOK_CONST }
| "const_cast"                    { TOK_CONST_CAST }
| "continue"                      { TOK_CONTINUE }
| "default"                       { TOK_DEFAULT }
| "delete"                        { TOK_DELETE }
| "do"                            { TOK_DO }
| "double"                        { TOK_DOUBLE }
| "dynamic_cast"                  { TOK_DYNAMIC_CAST }
| "else"                          { TOK_ELSE }
| "enum"                          { TOK_ENUM }
| "explicit"                      { TOK_EXPLICIT }
| "export"                        { TOK_EXPORT }
| "extern"                        { TOK_EXTERN }
| "false"                         { TOK_FALSE }
| "float"                         { TOK_FLOAT }
| "for"                           { TOK_FOR }
| "friend"                        { TOK_FRIEND }
| "goto"                          { TOK_GOTO }
| "if"                            { TOK_IF }
| "inline"                        { TOK_INLINE }
| "int"                           { TOK_INT }
| "long"                          { TOK_LONG }
| "mutable"                       { TOK_MUTABLE }
| "namespace"                     { TOK_NAMESPACE }
| "new"                           { TOK_NEW }
| "operator"                      { TOK_OPERATOR }
| "pascal"                        { TOK_PASCAL }
| "private"                       { TOK_PRIVATE }
| "protected"                     { TOK_PROTECTED }
| "public"                        { TOK_PUBLIC }
| "register"                      { TOK_REGISTER }
| "reinterpret_cast"              { TOK_REINTERPRET_CAST }
| "return"                        { TOK_RETURN }
| "short"                         { TOK_SHORT }
| "signed"                        { TOK_SIGNED }
| "sizeof"                        { TOK_SIZEOF }
| "static"                        { TOK_STATIC }
| "static_cast"                   { TOK_STATIC_CAST }
| "struct"                        { TOK_STRUCT }
| "switch"                        { TOK_SWITCH }
| "template"                      { TOK_TEMPLATE }
| "this"                          { TOK_THIS }
| "throw"                         { TOK_THROW }
| "true"                          { TOK_TRUE }
| "try"                           { TOK_TRY }
| "typedef"                       { TOK_TYPEDEF }
| "typeid"                        { TOK_TYPEID }
| "typename"                      { TOK_TYPENAME }
| "union"                         { TOK_UNION }
| "unsigned"                      { TOK_UNSIGNED }
| "using"                         { TOK_USING }
| "virtual"                       { TOK_VIRTUAL }
| "void"                          { TOK_VOID }
| "volatile"                      { TOK_VOLATILE }
| "wchar_t"                       { TOK_WCHAR_T }
| "while"                         { TOK_WHILE }
| "("                             { TOK_LPAREN }
| ")"                             { TOK_RPAREN }
| "["                             { TOK_LBRACKET }
| "]"                             { TOK_RBRACKET }
| "->"                            { TOK_ARROW }
| "::"                            { TOK_COLONCOLON }
| "."                             { TOK_DOT }
| "!"                             { TOK_BANG }
| "~"                             { TOK_TILDE }
| "+"                             { TOK_PLUS }
| "-"                             { TOK_MINUS }
| "++"                            { TOK_PLUSPLUS }
| "--"                            { TOK_MINUSMINUS }
| "&"                             { TOK_AND }
| "*"                             { TOK_STAR }
| ".*"                            { TOK_DOTSTAR }
| "->*"                           { TOK_ARROWSTAR }
| "/"                             { TOK_SLASH }
| "%"                             { TOK_PERCENT }
| "<<"                            { TOK_LEFTSHIFT }
| ">>"                            { TOK_RIGHTSHIFT }
| "<"                             { TOK_LESSTHAN }
| "<="                            { TOK_LESSEQ }
| ">"                             { TOK_GREATERTHAN }
| ">="                            { TOK_GREATEREQ }
| "=="                            { TOK_EQUALEQUAL }
| "!="                            { TOK_NOTEQUAL }
| "^"                             { TOK_XOR }
| "|"                             { TOK_OR }
| "&&"                            { TOK_ANDAND }
| "||"                            { TOK_OROR }
| "?"                             { TOK_QUESTION }
| ":"                             { TOK_COLON }
| "="                             { TOK_EQUAL }
| "*="                            { TOK_STAREQUAL }
| "/="                            { TOK_SLASHEQUAL }
| "%="                            { TOK_PERCENTEQUAL }
| "+="                            { TOK_PLUSEQUAL }
| "-="                            { TOK_MINUSEQUAL }
| "&="                            { TOK_ANDEQUAL }
| "^="                            { TOK_XOREQUAL }
| "|="                            { TOK_OREQUAL }
| "<<="                           { TOK_LEFTSHIFTEQUAL }
| ">>="                           { TOK_RIGHTSHIFTEQUAL }
| ","                             { TOK_COMMA }
| "..."                           { TOK_ELLIPSIS }
| ";"                             { TOK_SEMICOLON }
| "{"                             { TOK_LBRACE }
| "}"                             { TOK_RBRACE }
| "__attribute__"                 { TOK___ATTRIBUTE__ }
| "__FUNCTION__"                  { TOK___FUNCTION__ }
| "__label__"                     { TOK___LABEL__ }
| "__PRETTY_FUNCTION__"           { TOK___PRETTY_FUNCTION__ }
| "__typeof__"                    { TOK___TYPEOF__ }

(* C++ comments *)
| "//" [^ '\n']*                  { token lexbuf }

(* C comments *)
| "/*" ([^ '*']| "*"* [^ '*' '/'])* "*"+ "/"     { token lexbuf }
| "/*" ([^ '*']| "*"* [^ '*' '/'])* "*"*         { failwith "unterminated comment" }

(* identifier *)
['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '_' '0'-'9']*     { TOK_NAME }

(* integer literal *)
['1'-'9']['0'-'9']*{INT_SUFFIX}?           |
[0][0-7]*{INT_SUFFIX}?             |
[0][xX][0-9A-Fa-f]+{INT_SUFFIX}?   {



(* EOF *)
