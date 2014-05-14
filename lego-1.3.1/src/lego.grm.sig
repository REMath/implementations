signature Lego_TOKENS =
sig
type ('a,'b) token
type svalue
val app:  'a * 'a -> (svalue,'a) token
val VREG:  'a * 'a -> (svalue,'a) token
val UTAC:  'a * 'a -> (svalue,'a) token
val UPARR:  'a * 'a -> (svalue,'a) token
val EQUALITY:  'a * 'a -> (svalue,'a) token
val qNIFY:  'a * 'a -> (svalue,'a) token
val QNIFY:  'a * 'a -> (svalue,'a) token
val INVERT:  'a * 'a -> (svalue,'a) token
val INVERSION:  'a * 'a -> (svalue,'a) token
val INDUCTION:  'a * 'a -> (svalue,'a) token
val RECORD:  'a * 'a -> (svalue,'a) token
val THEOREMS:  'a * 'a -> (svalue,'a) token
val RELATION:  'a * 'a -> (svalue,'a) token
val CONSTRS:  'a * 'a -> (svalue,'a) token
val PARAMS:  'a * 'a -> (svalue,'a) token
val NOREDS:  'a * 'a -> (svalue,'a) token
val INDUCTIVE:  'a * 'a -> (svalue,'a) token
val UNSAFE:  'a * 'a -> (svalue,'a) token
val UNDO:  'a * 'a -> (svalue,'a) token
val UNFREEZE:  'a * 'a -> (svalue,'a) token
val UNDERSCORE:  'a * 'a -> (svalue,'a) token
val TAGEND:  'a * 'a -> (svalue,'a) token
val TAGBEGIN:  'a * 'a -> (svalue,'a) token
val TYPESTR:  'a * 'a -> (svalue,'a) token
val TYPEOF:  'a * 'a -> (svalue,'a) token
val TYPE:  'a * 'a -> (svalue,'a) token
val TREG:  'a * 'a -> (svalue,'a) token
val TILDE:  'a * 'a -> (svalue,'a) token
val THRY:  'a * 'a -> (svalue,'a) token
val ENDTHEORY:  'a * 'a -> (svalue,'a) token
val STTHEORY:  'a * 'a -> (svalue,'a) token
val TACTICTRY:  'a * 'a -> (svalue,'a) token
val TACTICTHEN:  'a * 'a -> (svalue,'a) token
val TACTICSUCCEED:  'a * 'a -> (svalue,'a) token
val TACTICREPEAT:  'a * 'a -> (svalue,'a) token
val TACTICFOR:  'a * 'a -> (svalue,'a) token
val TACTICFAIL:  'a * 'a -> (svalue,'a) token
val TACTICELSE:  'a * 'a -> (svalue,'a) token
val STARSQ:  'a * 'a -> (svalue,'a) token
val STRING: (string) *  'a * 'a -> (svalue,'a) token
val STARTTIMER:  'a * 'a -> (svalue,'a) token
val SLASHS:  'a * 'a -> (svalue,'a) token
val SEMICOLON:  'a * 'a -> (svalue,'a) token
val SAVEOBJECTSOFF:  'a * 'a -> (svalue,'a) token
val SAVEOBJECTSON:  'a * 'a -> (svalue,'a) token
val DOLLARSAVE:  'a * 'a -> (svalue,'a) token
val SAVEFROZEN:  'a * 'a -> (svalue,'a) token
val SAVEUNFROZ:  'a * 'a -> (svalue,'a) token
val SAVE:  'a * 'a -> (svalue,'a) token
val RIGHT:  'a * 'a -> (svalue,'a) token
val RELOAD:  'a * 'a -> (svalue,'a) token
val RSQBR:  'a * 'a -> (svalue,'a) token
val RRBR:  'a * 'a -> (svalue,'a) token
val RPTBR:  'a * 'a -> (svalue,'a) token
val RELINT: (bool*int) *  'a * 'a -> (svalue,'a) token
val REFINE:  'a * 'a -> (svalue,'a) token
val RCBR:  'a * 'a -> (svalue,'a) token
val QREPL:  'a * 'a -> (svalue,'a) token
val QM:  'a * 'a -> (svalue,'a) token
val PBPHYP:  'a * 'a -> (svalue,'a) token
val PBP:  'a * 'a -> (svalue,'a) token
val PCTPCT:  'a * 'a -> (svalue,'a) token
val PWD:  'a * 'a -> (svalue,'a) token
val PROP:  'a * 'a -> (svalue,'a) token
val PRINTTIMER:  'a * 'a -> (svalue,'a) token
val PRF:  'a * 'a -> (svalue,'a) token
val PPLINEWIDTH:  'a * 'a -> (svalue,'a) token
val PPON:  'a * 'a -> (svalue,'a) token
val PPOFF:  'a * 'a -> (svalue,'a) token
val ORIR:  'a * 'a -> (svalue,'a) token
val ORIL:  'a * 'a -> (svalue,'a) token
val ORE:  'a * 'a -> (svalue,'a) token
val NOTI:  'a * 'a -> (svalue,'a) token
val NOTE:  'a * 'a -> (svalue,'a) token
val NORMTYP:  'a * 'a -> (svalue,'a) token
val NORMAL:  'a * 'a -> (svalue,'a) token
val NEXT:  'a * 'a -> (svalue,'a) token
val MAKE:  'a * 'a -> (svalue,'a) token
val MARKS:  'a * 'a -> (svalue,'a) token
val MODULE:  'a * 'a -> (svalue,'a) token
val LEFT:  'a * 'a -> (svalue,'a) token
val LOAD:  'a * 'a -> (svalue,'a) token
val LSQBR:  'a * 'a -> (svalue,'a) token
val LRBR:  'a * 'a -> (svalue,'a) token
val LPTBR:  'a * 'a -> (svalue,'a) token
val LINE:  'a * 'a -> (svalue,'a) token
val LCBR:  'a * 'a -> (svalue,'a) token
val LOGIC:  'a * 'a -> (svalue,'a) token
val LABEL:  'a * 'a -> (svalue,'a) token
val KILLREF:  'a * 'a -> (svalue,'a) token
val INFIX_R9: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_L9: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_R8: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_L8: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_R7: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_L7: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_R6: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_L6: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_R5: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_L5: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_R4: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_L4: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_R3: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_L3: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_R2: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_L2: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_R1: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_L1: (string) *  'a * 'a -> (svalue,'a) token
val INFIX_UNREGD: (string) *  'a * 'a -> (svalue,'a) token
val INFIX:  'a * 'a -> (svalue,'a) token
val INTERACTIVE:  'a * 'a -> (svalue,'a) token
val IMPORT:  'a * 'a -> (svalue,'a) token
val iNTROS:  'a * 'a -> (svalue,'a) token
val INTROS:  'a * 'a -> (svalue,'a) token
val INT: (int) *  'a * 'a -> (svalue,'a) token
val INIT:  'a * 'a -> (svalue,'a) token
val IMPI:  'a * 'a -> (svalue,'a) token
val IMPE:  'a * 'a -> (svalue,'a) token
val IMMED:  'a * 'a -> (svalue,'a) token
val INCLUDE:  'a * 'a -> (svalue,'a) token
val ID: (string) *  'a * 'a -> (svalue,'a) token
val HNF:  'a * 'a -> (svalue,'a) token
val HELP:  'a * 'a -> (svalue,'a) token
val HASH:  'a * 'a -> (svalue,'a) token
val DOLLARGOAL:  'a * 'a -> (svalue,'a) token
val GOAL:  'a * 'a -> (svalue,'a) token
val GEN:  'a * 'a -> (svalue,'a) token
val GENERATE:  'a * 'a -> (svalue,'a) token
val FROM:  'a * 'a -> (svalue,'a) token
val FORGETMARK:  'a * 'a -> (svalue,'a) token
val FORGET:  'a * 'a -> (svalue,'a) token
val FREEZE:  'a * 'a -> (svalue,'a) token
val FIELDS:  'a * 'a -> (svalue,'a) token
val ENDCASE:  'a * 'a -> (svalue,'a) token
val EXPORTST:  'a * 'a -> (svalue,'a) token
val EXPAND:  'a * 'a -> (svalue,'a) token
val EXPALL:  'a * 'a -> (svalue,'a) token
val EXI:  'a * 'a -> (svalue,'a) token
val EXE:  'a * 'a -> (svalue,'a) token
val EQUIV:  'a * 'a -> (svalue,'a) token
val EQUAL:  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
val ELIM:  'a * 'a -> (svalue,'a) token
val ECHO:  'a * 'a -> (svalue,'a) token
val DOUBLE:  'a * 'a -> (svalue,'a) token
val DECLS:  'a * 'a -> (svalue,'a) token
val DOT2:  'a * 'a -> (svalue,'a) token
val DOT1:  'a * 'a -> (svalue,'a) token
val DOT:  'a * 'a -> (svalue,'a) token
val DNF:  'a * 'a -> (svalue,'a) token
val DISCHARGEKEEP:  'a * 'a -> (svalue,'a) token
val DISCHARGE:  'a * 'a -> (svalue,'a) token
val DOLLARSQ:  'a * 'a -> (svalue,'a) token
val DEQ:  'a * 'a -> (svalue,'a) token
val CASE:  'a * 'a -> (svalue,'a) token
val CUT:  'a * 'a -> (svalue,'a) token
val CHOICE:  'a * 'a -> (svalue,'a) token
val CTXT:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val CONTRACT:  'a * 'a -> (svalue,'a) token
val CONFIG:  'a * 'a -> (svalue,'a) token
val COLON:  'a * 'a -> (svalue,'a) token
val CLAIM:  'a * 'a -> (svalue,'a) token
val CD:  'a * 'a -> (svalue,'a) token
val BAR:  'a * 'a -> (svalue,'a) token
val BACKSLASH:  'a * 'a -> (svalue,'a) token
val ASSUMPTION:  'a * 'a -> (svalue,'a) token
val ANNOTATEOFF:  'a * 'a -> (svalue,'a) token
val ANNOTATEON:  'a * 'a -> (svalue,'a) token
val ARROW:  'a * 'a -> (svalue,'a) token
val ANDI:  'a * 'a -> (svalue,'a) token
val ANDE:  'a * 'a -> (svalue,'a) token
val ALLI:  'a * 'a -> (svalue,'a) token
val ALLE:  'a * 'a -> (svalue,'a) token
end
signature Lego_LRVALS=
sig
structure Tokens : Lego_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
