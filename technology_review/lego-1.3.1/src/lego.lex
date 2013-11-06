(* lego.lex *)

structure Tokens = Tokens
open Tokens

structure Pos = Pos
open Pos

open Infix

type pos = Pos.pos
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

fun eof() = EOF(!lno,!lno)


structure KeyWord : sig
		      val find : string -> ((pos*pos)->lexresult) option
	  	    end =
  struct

	val TableSize = 401
	val HashFactor = 7

	val hash = fn s =>
	   fold (fn (c,v)=>(v*HashFactor+(ord c)) mod TableSize) (explode s) 0


	val HashTable = Array.array(TableSize,nil) :
		 (string * ((pos*pos)->lexresult)) list Array.array


	val add = fn (s,v) =>
	 let val i = hash s
	 in Array.update(HashTable,i,(s,v) :: (Array.sub(HashTable, i)))
	 end

        val find = fn s =>
	  let val i = hash s
	      fun f ((key,v)::r) = if s=key then SOME v else f r
	        | f nil = NONE
	  in  f (Array.sub(HashTable, i))
	  end
 
	val _ = 
	    (List.app add
        [("allE", ALLE),
         ("allI", ALLI),
         ("andE", ANDE),
         ("andI", ANDI),
	 ("AnnotateOn", ANNOTATEON),
	 ("AnnotateOff", ANNOTATEOFF),
	 ("Assumption", ASSUMPTION),
	 ("Double", DOUBLE),
         ("Cd", CD),
         ("Claim", CLAIM),
	 ("Configure", CONFIG),
         ("Ctxt", CTXT),
         ("Cut", CUT),
	 ("Fields", FIELDS),
         ("Inductive", INDUCTIVE),
         ("NoReductions", NOREDS),
         ("Parameters", PARAMS),
         ("Constructors", CONSTRS),
         ("Decls", DECLS),
         ("Discharge", DISCHARGE),
         ("DischargeKeep", DISCHARGEKEEP),
         ("Dnf", DNF),
	 ("Drop", EOF),
         ("echo", ECHO),
         ("Elim", ELIM),
         ("Equality", EQUALITY),
         ("Equiv", EQUIV),
         ("exI", EXI),
         ("exE", EXE),
         ("ExpAll", EXPALL),
         ("Expand", EXPAND),
         ("ExportState", EXPORTST),
         ("EndCase", ENDCASE),
         ("Forget", FORGET),
         ("ForgetMark", FORGETMARK),
         ("Freeze", FREEZE),
         ("From", FROM),
         ("Unfreeze", UNFREEZE),
         ("Gen", GEN),
         ("Generate", GENERATE),
         ("Goal", GOAL),
         ("Help", HELP),
         ("Hnf", HNF),
         ("Include", INCLUDE),
         ("Interactive", INTERACTIVE),
         ("Immed", IMMED),
         ("impE", IMPE),
         ("impI", IMPI),
         ("Init", INIT),
         ("Intros", INTROS),
         ("intros", iNTROS),
         ("Import", IMPORT),
         ("Induction", INDUCTION),
         ("Infix", INFIX),
         ("Inversion", INVERSION),
         ("Invert", INVERT),
         ("KillRef", KILLREF),
         ("Label", LABEL),
         ("Logic", LOGIC),
         ("left", LEFT),
         ("line", LINE),
         ("Load", LOAD),
         ("Marks", MARKS),
         ("Make", MAKE),
         ("Module", MODULE),
         ("Next", NEXT),
         ("Normal", NORMAL),
         ("NormTyp", NORMTYP),
         ("notE", NOTE),
         ("notI", NOTI),
         ("orE", ORE),
         ("orIL", ORIL),
         ("orIR", ORIR),
         ("Pbp", PBP),
         ("PbpHyp", PBPHYP),
	 ("PrettyOff", PPOFF),
	 ("PrettyOn", PPON),
	 ("PrettyWidth", PPLINEWIDTH),
         ("Prf", PRF),
         ("Prop", PROP),
         ("Pwd", PWD),
         ("Qnify", QNIFY),
         ("qnify", qNIFY),
	 ("Qrepl", QREPL),
         ("Refine", REFINE),
         ("Reload", RELOAD),
         ("right", RIGHT),
         ("Save", SAVE),
         ("SaveUnfrozen", SAVEUNFROZ),
         ("SaveFrozen", SAVEFROZEN),
         ("SaveObjectsOn", SAVEOBJECTSON),
         ("SaveObjectsOff", SAVEOBJECTSOFF),
         ("Relation", RELATION),
         ("Theorems", THEOREMS),
         ("Theory", THRY),
	 ("StartTheory", STTHEORY),
	 ("EndTheory", ENDTHEORY),
         ("Record",RECORD),
         ("StartTimer", STARTTIMER),
         ("PrintTimer", PRINTTIMER),
	 ("Else", TACTICELSE),
	 ("Fail", TACTICFAIL),
	 ("For", TACTICFOR),
	 ("Repeat", TACTICREPEAT),
	 ("Succeed", TACTICSUCCEED),
	 ("Then", TACTICTHEN),
	 ("Try", TACTICTRY),
         ("TReg", TREG),
         ("Type", TYPE),
         ("ElimOver", TYPESTR),
         ("TypeOf", TYPEOF),
         ("Undo", UNDO),
         ("Unsafe", UNSAFE),
	 ("UTac", UTAC),
         ("VReg", VREG)
        ]) 
   end
   open KeyWord


val commentLevel = ref 0

fun makeInt (s : string) =
    (revfold (fn (c,a) => a*10 + (ord c - ord("0"))) (explode s) 0)


%%
%s C D;
%header (functor LegoLexFun(structure Tokens:Lego_TOKENS
                            structure Pos:POS
                            structure Infix: INFIX):LEXER);

alpha = [A-Za-z];
digit = [0-9];
ws = [\ \t];
infsym = [+-/*]|"<<"|">>"|"/\\"|"\\/"|"|-"|"::"|&[a-zA-Z]+|@[a-zA-Z]+;

%%
<INITIAL>\n        => (inc_lno(); lex());
<INITIAL>{ws}+     => (lex());
<INITIAL>"//"      => (SLASHS(!lno,!lno));
<INITIAL>"->"      => (ARROW(!lno,!lno));
<INITIAL>"\\"      => (BACKSLASH(!lno,!lno));
<INITIAL>"||"      => (CHOICE(!lno,!lno));
<INITIAL>"|"       => (BAR(!lno,!lno));
<INITIAL>":"       => (COLON(!lno,!lno));
<INITIAL>","       => (COMMA(!lno,!lno));
<INITIAL>"==>"     => (CONTRACT(!lno,!lno));
<INITIAL>"(!"      => (TAGBEGIN(!lno,!lno));
<INITIAL>"!)"      => (TAGEND(!lno,!lno));
<INITIAL>"(*"      => (YYBEGIN C; commentLevel := 1; lex());
<INITIAL>"%\\"     => (YYBEGIN D; lex());
<INITIAL>"=="      => (DEQ(!lno,!lno));
<INITIAL>".1"      => (DOT1(!lno,!lno));
<INITIAL>".2"      => (DOT2(!lno,!lno));
<INITIAL>"."       => (DOT(!lno,!lno));
<INITIAL>"^"       => (UPARR(!lno,!lno));
<INITIAL>"="       => (EQUAL(!lno,!lno));
<INITIAL>"#"       => (HASH(!lno,!lno));
<INITIAL>"{"       => (LCBR(!lno,!lno));
<INITIAL>"<"       => (LPTBR(!lno,!lno));
<INITIAL>"("       => (LRBR(!lno,!lno));
<INITIAL>"$["      => (DOLLARSQ(!lno,!lno));
<INITIAL>"*["      => (STARSQ(!lno,!lno));
<INITIAL>"$Save"   => (DOLLARSAVE(!lno,!lno));
<INITIAL>"$Goal"   => (DOLLARGOAL(!lno,!lno));
<INITIAL>"%%"      => (PCTPCT(!lno,!lno));
<INITIAL>"["       => (LSQBR(!lno,!lno));
<INITIAL>"?"       => (QM(!lno,!lno));
<INITIAL>"}"       => (RCBR(!lno,!lno));
<INITIAL>">"       => (RPTBR(!lno,!lno));
<INITIAL>")"       => (RRBR(!lno,!lno));
<INITIAL>"]"       => (RSQBR(!lno,!lno));
<INITIAL>";"       => (SEMICOLON(!lno,!lno));
<INITIAL>"~"       => (TILDE(!lno,!lno));
<INITIAL>"_"       => (UNDERSCORE(!lno,!lno));
<INITIAL>"[!"      => (CASE(!lno,!lno));
<INITIAL>"!]"      => (ENDCASE(!lno,!lno));
<INITIAL>{infsym}  => (
   (case Infix.infix_data yytext of 
     (LAssoc,n) => (nth [INFIX_L1, INFIX_L2, INFIX_L3, INFIX_L4,INFIX_L5,
                        INFIX_L6, INFIX_L7, INFIX_L8, INFIX_L9] n)
                        (yytext,!lno,!lno)
  |  (RAssoc,n) => (nth [INFIX_R1, INFIX_R2, INFIX_R3, INFIX_R4,INFIX_R5,
                        INFIX_R6, INFIX_R7, INFIX_R8, INFIX_R9] n)
                        (yytext,!lno,!lno)
  |  (_,_) => INFIX_UNREGD(yytext,!lno,!lno)));

<INITIAL>{digit}+  => (INT (makeInt yytext,!lno,!lno));
<INITIAL>"+"{digit}+  =>
       (RELINT ((false,makeInt (substring (yytext,1,size(yytext)-1))),!lno,!lno));
<INITIAL>"-"{digit}+  =>
       (RELINT ((true,makeInt (substring (yytext,1,size(yytext)-1))),!lno,!lno));<INITIAL>"\""[^\n\"]*"\""  =>
       (STRING (substring (yytext,1,size(yytext)-2),!lno,!lno));
<INITIAL>"op"{infsym}({alpha}|{digit}|"_"|"'")* => (ID(yytext,!lno,!lno));
<INITIAL>{alpha}+  => (case  KeyWord.find yytext
	                 of SOME v => v (!lno,!lno)
	                  | _ => ID (yytext,!lno,!lno));
<INITIAL>{alpha}({alpha}|{digit}|"_"|"'")* => (ID (yytext,!lno,!lno));

<INITIAL>.         => (errmsg "Lego lexer"
	                      ("ignoring bad character "^yytext,!lno,!lno); 
                       lex());

<C>"(*"		   => (commentLevel := !commentLevel+1; lex());
<C>"*)"		   => (commentLevel := !commentLevel-1;
                       if (!commentLevel=0) then YYBEGIN INITIAL else ();
		       lex());
<C>\n		   => (inc_lno(); lex());
<C>.		   => (lex());

<D>.*\n            => (inc_lno(); YYBEGIN INITIAL; lex());
