/*
 * SSL.g - This file is part of the Jakstab project.
 * 
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 * Copyright 2006 Jose Fonseca
 *
 * The original grammar was taken from the IDC - Interactive Decompiler
 * project by J. Fonseca. It was ported to Java and heavily modified 
 * for use with Jakstab by J. Kinder. 
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, see <http://www.gnu.org/licenses/>.
 */


/*
 * ANTLR grammar for the Semantics Specification Language (SSL)
 *
 * Based on
 *  C. Cifuentes and S. Sendall. Specifying the semantics of machine instructions. 
 *  In Proc. Int'l Workshop on Program Comprehension, pp. 126-133, Ischia, Italy, 
 *  24-26 June 1998, IEEE Computer Society.
 * and on the files:
 * sslscanner.l and sslparser.y from UQBT source distribution.
 * sslscanner.l and sslparser.y from boomerang source distribution.
 */

header {
	package org.jakstab.ssl.parser;
}

////////////////////////////////////////////////////////////////////////////////
// Parser
////////////////////////////////////////////////////////////////////////////////

{
	import java.util.*;

	@SuppressWarnings("all")
}
class SSLParser extends Parser;
options {
	buildAST = true;
	k = 3;
	defaultErrorHandler = true;
}

{
	// Begin parser
}


start
	: specification EOF!
	;

specification
	: ( part SEMI! )*
		{ ## = #(#[SEMI,"SEMI"], ##); }
	;

part
	: const_def	
	| registers_decl 
	| operands_decl	
	| endianness	
	| function_def 
	| table_def	
	| instr_def	
	| fast_list
	;

num: NUM;

const_def
	: NAME EQUATE! v:const_expr
		{ ## = #(#[CONSTANT,"CONSTANT"], ##); }
	;

const_expr
	: NUM ((PLUS^|MINUS^) NUM)*
	;

registers_decl
	: ("INTEGER"| "FLOAT") register_decl (COMMA! register_decl)*
		{ ## = #(#[REGDECL,"REGDECL"], ##); }
	;

register_decl
	: REG_ID ^INDEX num
	| REG_ID LSQUARE num RSQUARE INDEX num
		( "COVERS" REG_ID TO REG_ID
		| "SHARES" REG_ID AT LSQUARE num TO num RSQUARE
		)?
	| LSQUARE register_list RSQUARE LSQUARE num RSQUARE INDEX num (TO num)?
	;

register_list
	: REG_ID (COMMA! REG_ID)*
	;

operands_decl
	: "OPERAND"^ operand_decl ( COMMA! operand_decl )*
	;

operand_decl
	: NAME^ EQUATE LCURLY! param_list RCURLY!
	| NAME^ param_list (LSQUARE param_list RSQUARE)? ASSIGNTYPE expr
	;

endianness: "ENDIANNESS"^ ( "BIG" | "LITTLE" );

function_def
	: NAME LPAREN! param_list RPAREN! LCURLY! rt_list RCURLY!
		{ ## = #(#[FUNCTION,"FUNCTION"], ##); }
	;

table_def
	: NAME EQUATE! table_expr
		{ ## = #(#[TABLE,"TABLE"], ##); }
	;

table_expr
	: (str_table_expr) => str_table_expr
	| op_str_table
	| expr_str_table
	;

str_table_expr
	: str_table (str_table
		{ ## = #(#[CROSSP,"CROSSP"], ##); } /* Cross product */
	  )*
	;

str_table
	: NAME
	| LCURLY^ str_entry (COMMA! str_entry)* RCURLY!
	;

str_entry
	: NAME
	| QUOTE QUOTE! { ## = #(##, #[NAME,""]); }
	| QUOTE^ NAME QUOTE!
	| QUOTE^ DECOR QUOTE!
	;

op_str_table
	: LCURLY^ op_str_entry (COMMA! t:op_str_entry)* RCURLY!
	;

op_str_entry
	: QUOTE^ bin_oper QUOTE!
	;

bin_oper
	: MOD | MUL | DIV | SMUL | SDIV | SMOD | PLUS | MINUS
	| "rlc" | "rrc" | "rl" | "rr" | RSHIFT | LSHIFT | RSHIFTA | OR | ORNOT | AND | ANDNOT | XOR | XORNOT
	| MUL_F | MUL_FD | MUL_FQ | MUL_FSD | MUL_FDQ | DIV_F | DIV_FD | DIV_FQ | PLUS_F | PLUS_FD | PLUS_FQ | MINUS_F | MINUS_FD | MINUS_FQ | "pow"
	| EQ | NE | LT | GT | LE | GE | LTU | GTU | LEU | GEU
	;

expr_str_table
	: LCURLY^ expr_str_entry (COMMA! t:expr_str_entry)* RCURLY!
	;

expr_str_entry
	: QUOTE^ expr QUOTE!
	;

instr_def
	: instr_name param_list rt_list
		{ ## = #(#[INSTR,"INSTR"], ##); }
	;

instr_name
	: instr_name_head instr_name_tail (instr_name_decor)*
		{ ## = #(#[INSTR_NAME,"INSTR_NAME"], ##); }
	;

instr_name_head
	: (instr_name_elem) => instr_name_elem instr_name_tail
	| NAME^
	;

instr_name_elem
	: PRIME^ NAME PRIME!
	| QUOTE! NAME^ QUOTE!
	| NAME LSQUARE^ (num|NAME) RSQUARE!
	| DOLLAR! NAME LSQUARE^ (num|NAME) RSQUARE!
	;

instr_name_tail
	: (instr_name_elem) => instr_name_elem instr_name_tail
	|
	;

instr_name_decor
	: DECOR^
	;

// register transfer list
rt_list
	: (rt)+
		{ ## = #(#[RTL,"RTL"], ##); }
	;

rt
	: assign_rt
	| NAME LPAREN! expr_list RPAREN! { ## = #(#[FUNCTION,"FUNCTION"], ##); }
//	| ("undefineflags"^| "defineflags"^) LPAREN! (REG_ID ( COMMA! REG_ID)* )? RPAREN!
	| "halt"^
	| UNDERSCORE!
	;

param_list
	: ((NAME) => NAME (COMMA! t:NAME)* | )
		{ ## = #(#[COMMA,","], ##); }
	;

assign_rt
	: ASSIGNTYPE^ expr EQUATE! expr
	| "MEMSET"^ expr COMMA! expr COMMA! expr
	| "MEMCPY"^ expr COMMA! expr COMMA! expr
//	| ASSIGNTYPE^ expr THEN var EQUATE! expr
//	| ASSIGNTYPE^ expr
//	| "FPUSH"^
//	| "FPOP"^
	;

var
	:
		( REG_ID^
		| REG_IDX^ LSQUARE! expr RSQUARE!
		| MEM_IDX^ LSQUARE! expr RSQUARE!
		| NAME^
		)
		( AT^ LSQUARE! expr COLON! expr RSQUARE!
		| PRIME^
		)*
	;

primary_expr
	: NUM^
	| FLOATNUM^
//	| TEMP
	| REG_ID^
	| REG_IDX^ LSQUARE! expr RSQUARE!
	| MEM_IDX^ LSQUARE! expr RSQUARE!
	| NAME^
	| NAME LSQUARE^ (NAME|NUM) RSQUARE!
	| LPAREN! expr RPAREN!
	| LSQUARE! expr QUEST^ expr COLON! expr RSQUARE!
	| NAME LPAREN! expr_list RPAREN! { ## = #([BUILTIN,"BUILTIN"], ##); }
	;

// bit extraction, sign extension, cast
postfix_expr
	: primary:primary_expr
		( (AT) => AT^ LSQUARE! expr COLON! expr RSQUARE!
		| (S_E) => S_E^
//		| (LCURLY num RCURLY) => LCURLY^ num RCURLY!
		| (!LCURLY width:num !RCURLY) { ## = #([CAST,"CAST"], #width, ##); }
		)*
	;

// operator lookup
lookup_expr
	: postfix_expr
		( (NAME LSQUARE NAME RSQUARE) => NAME LSQUARE! NAME RSQUARE! lookup_expr
			{ ## = #([LOOKUP_OP,"LOOKUP_OP"], ##); }
		|
		)
	;

// not
unary_expr
	: (NOT^ | FNEG^ | LNOT^)* lookup_expr
	;

// floating point arithmetic
fp_expr
	: unary_expr ((MUL_F^ | MUL_FD^ | MUL_FQ^ | MUL_FSD^ | MUL_FDQ^ | DIV_F^ | DIV_FD^ | DIV_FQ^ | PLUS_F^ | PLUS_FD^ | PLUS_FQ^ | MINUS_F^ | MINUS_FD^ | MINUS_FQ^ | "pow"^) unary_expr)*
	;

// arithmetic
arith_expr
	: fp_expr ((MOD^ | MUL^ | DIV^ | SMUL^ | SDIV^ | SMOD^ | PLUS^ | MINUS^) fp_expr)*
	;

// bit arithmetic
bit_expr
	: arith_expr (("rlc"^ | "rrc"^ | "rl"^ | "rr"^ | RSHIFT^ | LSHIFT^ | RSHIFTA^ | OR^ | ORNOT^ | AND^ | ANDNOT^ | XOR^ | XORNOT^) arith_expr)*
	;

// conditionals
cond_expr
	: bit_expr ((EQ^ | NE^ | LT^ | GT^ | LE^ | GE^ | LTU^ | GTU^ | LEU^ | GEU^) bit_expr)*
	;

// logicals
log_expr
	: cond_expr ((LAND^ | LOR^) cond_expr)*
	;

expr: log_expr;

expr_list: (expr (COMMA! expr)* )?;

fast_list: "FAST"^ fast_entry (COMMA! fast_entry)*;

fast_entry: NAME INDEX^ NAME;


////////////////////////////////////////////////////////////////////////////////
// Lexer
////////////////////////////////////////////////////////////////////////////////

{
	@SuppressWarnings("all")
}
class SSLLexer extends Lexer;

options {
	k = 4;
	testLiterals=true;
}

tokens {
	CONSTANT;
	TABLE;
	CROSSP;
	FUNCTION;
	INSTR;
	INSTR_NAME;
	LOOKUP_OP;
	RTL;
	BUILTIN;
	CAST;
	REGDECL;
/*}

tokens {*/
	REG_IDX="r";
	MEM_IDX="m";
	LAND="and";
	LOR="or";
}

// Whitespace -- ignored
WS
	: (' '|'\t'|'\f')+ { $setType(Token.SKIP); }
	| ( '\r' ('\n')? | '\n') { newline(); $setType(Token.SKIP); }
	;

// Single-line comments
COMMENT
	:	"#"
		(~('\n'|'\r'))* ('\n'|'\r'('\n')?)?
		{ newline(); $setType(Token.SKIP); }
	;

protected DIGITS:	('0'..'9')+	;
protected HEXDIGITS: ('0'..'9'|'A'..'F'|'a'..'f')+;

protected NUM	
	{boolean positive = true; java.math.BigInteger v=null;}
	:  
		(
		|'-'! { positive=false; }
		)
		( DIGITS { v = new java.math.BigInteger($getText); }
		| "0x"! HEXDIGITS { v = new java.math.BigInteger($getText, 16); }
		| "2**"! DIGITS { v = (java.math.BigInteger.valueOf(2)).pow(Integer.parseInt($getText)); }
		)
		{ setText(positive ? v.toString() : ('-' + v.toString() ) ); }
	;

/*
protected
NUM	:
		( { s = 1 }
		|'-'! { s = -1 }
		)
		( ('0'..'9')+ { v = int($getText) }
		| "0x"! ('0'..'9'|'A'..'F')+ { v = int($getText, 16) }
		| "2**"! ('0'..'9')+ { v = 2**int($getText) }
		)
		{ v = str(v*s); $setText(v) }
	;
*/

protected
FLOATNUM
	: ('-')? ('0'..'9')+ '.' ('0'..'9')+ ( ('e'|'E') NUM )?
	;

FLOAT_OR_NUM
	: (FLOATNUM ) => FLOATNUM { $setType(FLOATNUM); }
	| (NUM) => NUM { $setType(NUM); }
	| (MINUS) => MINUS { $setType(MINUS); }
	;

NAME
	: ('A'..'Z'|'a'..'z')('A'..'Z'|'a'..'z'|'0'..'9'|'_')*
	;

REG_ID
	:  '%' ('A'..'Z'|'a'..'z')('A'..'Z'|'a'..'z'|'0'..'9')*
	;

DECOR
	: '.' ('A'..'Z'|'a'..'z')('A'..'Z'|'a'..'z'|'.'|'0'..'9')*
	;

COLON: ':';
EQUATE: ":=";
ASSIGN: "::=";
SEMI: ';';

COMMA: ',';

LPAREN: '(';
RPAREN: ')';
LSQUARE: '[';
RSQUARE: ']';
LCURLY: '{';
RCURLY: '}';

INDEX: "->";
THEN: "=>";
TO: "..";
AT: '@';

protected
ASSIGNTYPE: '*' ('a'..'z')? ('0'..'9')* '*';

ASSIGNTYPE_OR_MUL
	: ( ASSIGNTYPE ) => ASSIGNTYPE { $setType(ASSIGNTYPE); }
	| MUL { $setType(MUL); }
	| SMUL { $setType(SMUL); }
	| MUL_F { $setType(MUL_F); }
	| MUL_FD { $setType(MUL_FD); }
	| MUL_FQ { $setType(MUL_FQ); }
	| MUL_FSD { $setType(MUL_FSD); }
	| MUL_FDQ { $setType(MUL_FDQ); }
	;

PRIME: '\'';

NOT: '~';
OR: '|';
AND: '&';
XOR
	: '^'
		( ('"' ('A'..'Z'|'a'..'z')('A'..'Z'|'a'..'z')* '"') =>
			'"'! ('A'..'Z'|'a'..'z')('A'..'Z'|'a'..'z')* '"'! { $setType(DECOR); }
		| )
	;

ORNOT: "|~";
ANDNOT: "&~";
XORNOT: "^~";

PLUS: '+';
protected
MINUS: '-';
protected
MUL: '*';
DIV: '/';
MOD: '%';
protected
SMUL: "*!";
SDIV: "/!";
SMOD: "%!";

EQ: '=';
NE: "~=";
LT: '<';
GT: '>';
LE: "<=";
GE: ">=";
LTU: "<u";
GTU: ">u";
LEU: "<=u";
GEU: ">=u";

LSHIFT: "<<";
RSHIFTA: ">>A";
RSHIFT: ">>";

// Float operations
protected
MUL_F: "*f";
protected
MUL_FD: "*fd";
protected
MUL_FQ: "*fq";
protected
MUL_FSD: "*fsd";
protected
MUL_FDQ: "*fdq";
DIV_F: "/f";
DIV_FD: "/fd";
DIV_FQ: "/fq";
PLUS_F: "+f";
PLUS_FD: "+fd";
PLUS_FQ: "+fq";
MINUS_F: "-f";
MINUS_FD: "-fd";
MINUS_FQ: "-fq";

QUEST: '?';
S_E: '!';

DOT: '.';
QUOTE: '"';

DOLLAR: '$';

UNDERSCORE: '_';

FNEG: "~f";
LNOT: "~L";


////////////////////////////////////////////////////////////////////////////////
// Preprocessor
////////////////////////////////////////////////////////////////////////////////

{
	import java.util.*;
	import org.jakstab.rtl.*;
	import org.jakstab.rtl.expressions.*;
	import org.jakstab.rtl.statements.*;

	@SuppressWarnings("all")
}
class SSLPreprocessor extends TreeParser;

options {
	buildAST = true;
	defaultErrorHandler = false;
}


{
	private Map<String,Long> constants = new HashMap<String,Long>();
	private Map<String,List<AST>> tables = new HashMap<String,List<AST>>();
	private Map<String,SSLFunction> functions = new HashMap<String,SSLFunction>();
	private Map<String,SSLFunction> instructions = new TreeMap<String,SSLFunction>();
	private Stack<Map<String,AST>> locals = new Stack<Map<String,AST>>();
	private SetOfVariables registers = new SetOfVariables(); 

	public SetOfVariables getRegisters() { return registers; }	
	//public Map<String,SSLFunction> getFunctions() { return functions; }
	public Map<String,SSLFunction> getInstructions() { return instructions; }

	public Map<String,List<AST>> getTables() { return tables; }
	
}

start
	: specification
	;

specification
	: #( SEMI (part)* )
	;


/*
 * Parses a syntactic element of an SSL specification file.
 */
part  { 
		long lv=0; 
		List<AST> tv; 
		List<String> pl; 
		List<SSLInstructionName> inam; 
	} 
	: !#(CONSTANT cn:NAME lv=const_expr) {
			constants.put(cn.getText(), Long.valueOf(lv));
		}
	|! #(REGDECL ("INTEGER" | "FLOAT") (register_decl)*)
	|! #(TABLE tn:NAME tv=table_expr) { 
			tables.put(tn.getText(), tv); 
		}
	|! #(FUNCTION fn:NAME pl=param_list fb:RTL)
		{ functions.put(fn.getText(), new SSLFunction(fn.getText(), pl, astFactory.dupTree(fb))); }
	|! #(INSTR inam=instr_name pl=param_list ib:RTL)
		{
			for (SSLInstructionName in : inam) {
                if (in.getVarMap() != null) 
                	locals.push(in.getVarMap()); 
                else 
                	locals.push(new HashMap<String,AST>());
                rtl_expand(astFactory.dupTree(ib));
                locals.pop();
                AST rtl = getAST();

                if (instructions.containsKey(in.getName())) {
                    SSLFunction oldIns = instructions.get(in.getName());
/*                    if (oldpl != old_ip: TODO: JK - Check parameter list
                        throw new SemanticException(#ib, "parameter list of '%s' changed" % n)*/
                    if (rtl.getFirstChild() != null)
                        oldIns.getAST().addChild(rtl.getFirstChild());
                } else
                    instructions.put(in.getName(), new SSLFunction(in.getName(), pl, rtl));
			}
		}
//	| #( . ( . )* )
		// copy other parts unmodified
	;
	
register_decl! {
		int bitWidth; int regIdFrom; int regIdTo; int shareFrom = -1; int shareTo = -1;
		List<String> regList;
	}
	:
		INDEX r1:REG_ID regIdFrom=intValue {
				registers.add((RTLVariable)ExpressionFactory.createRegisterVariable(r1.getText(), RTLVariable.UNKNOWN_BITWIDTH));
		}
		
		| r2:REG_ID LSQUARE bitWidth=intValue RSQUARE INDEX regIdFrom=intValue
			( "COVERS" coveredRegFrom:REG_ID TO coveredRegTo:REG_ID
				| "SHARES" sharedReg:REG_ID AT LSQUARE shareFrom=intValue TO shareTo=intValue RSQUARE
			)? {
				if (coveredRegFrom != null) 
					throw new RuntimeException("COVERS not yet supported!");
				if (sharedReg != null) {
					ExpressionFactory.createSharedRegisterVariable(r2.getText(), sharedReg.getText(), shareFrom, shareTo);
				} else {
					registers.add((RTLVariable)ExpressionFactory.createRegisterVariable(r2.getText(), bitWidth));
				}
			}
		
		| LSQUARE regList=register_list RSQUARE LSQUARE bitWidth=intValue RSQUARE INDEX regIdFrom=intValue (TO regIdTo=intValue)? {
			for (String regName : regList) {
				registers.add((RTLVariable)ExpressionFactory.createRegisterVariable(regName, bitWidth));
			}
		}
	;

register_list! returns [List<String> res = new LinkedList<String>()]
	: r:REG_ID { res.add(r.getText()); } (rn:REG_ID { res.add(rn.getText()); })*
	;

/*
 * Parses a constant definition, calculating simple arithmetic on the fly.
 */
const_expr! returns [long v=0]
{ long l,r; }
	: n:NUM
		{ v = Long.parseLong(n.getText()); }
	| #(PLUS l=const_expr r=const_expr)
		{ v = l + r; }
	| #(MINUS l=const_expr r=const_expr)
		{ v = l - r; }
	;


/*
 * Parses the contents of a table into a list of ASTs.
 */
table_expr! returns [List<AST> res = null]
{ List<AST> h,t; }
	: 
	/* A curly bracketed list of elements can contain other table references */
	  #( LCURLY h=table_expr {
	  		res = new LinkedList<AST>(h); /* Copy so we don't change the other table! */ 
	  	} (t=table_expr { res.addAll(t); })* )
	/* The cross product of two tables */
	| #( CROSSP h=table_expr { res = h; } (t=table_expr {
			res = new LinkedList<AST>(); 
			for (AST tt : t) for (AST hh : h)
				res.add(astFactory.create(NAME, hh.getText() + tt.getText())); 
		}) )
	| #( QUOTE any:. ) { res = new LinkedList<AST>(); res.add(astFactory.dupTree(any)); }
	| n:NAME { 
		if (tables.containsKey(n.getText())) 
			res = tables.get(n.getText());
		else { res = new LinkedList<AST>(); res.add(n); 
			/*  lax specification of SSL seems to allow missing quotes? treat as string literal. 
			   throw new RecognitionException("Undefined table reference " + n.getText() + "!"); */ 
		}
	  }
	;
	
	
/*
 * Parses comma separated parameters into a list of Strings. 
 */
param_list! returns [List<String> res = null]
	: #(COMMA { res = new LinkedList<String>(); } ( n:NAME { res.add(n.getText()); } )* )
	;


/*
 * Parses an instruction name possibly containing multiple table lookups. If
 * the instruction name contains more than one table lookup, the cross product
 * of the instruction name elments is calculated.
 *
 * Returns a list of ('name', 'variables') pairs, where 'name' is the resolved
 * instruction name and 'variables' is a dict mapping the corresponding
 * variables/values resulting from table lookup.
 */
instr_name! returns [List<SSLInstructionName> res = null;]
{ List<SSLInstructionName> e; }
	: #( INSTR_NAME
		{ res = new LinkedList<SSLInstructionName>(); }
		( e=instr_name_elem
			{
				// If this is the first element, set result to this element's return value e.
				if (res.size() == 0) 
					res = e;
				// Otherwise, do a cross product of the previous result with e
				else {
                	List<SSLInstructionName> tmp = new LinkedList<SSLInstructionName>();
    	            for (SSLInstructionName lhsIn : res) {
        	            for (SSLInstructionName rhsIn : e) {
                	        Map newMap = new HashMap();
                	        if (lhsIn.getVarMap() != null) newMap.putAll(lhsIn.getVarMap());
                	        if (rhsIn.getVarMap() != null) newMap.putAll(rhsIn.getVarMap());
	                        tmp.add(new SSLInstructionName(lhsIn.getName() + rhsIn.getName(), newMap));
        	            }
            	    } 
                	res = tmp;
				}
			}
		)*
	)
	;


/*
 * Parses an element of an instruction name containing a single table lookup.
 * Returns a list of ('name', 'variables') pairs, where 'name' is the part of 
 * the name that is already resolved, and where 'variables' is a dict mapping 
 * the corresponding variables/values resulting from table lookup.
 */
instr_name_elem! returns [List<SSLInstructionName> res = null;]
{ 
	res = new LinkedList<SSLInstructionName>();
	List<AST> table = null;
}
	: name:NAME
		{ 	
			res.add(new SSLInstructionName(name.getText())); 
		}
//	| PRIME optname:NAME
//		{ res = [("", {}), (#optname.getText(), {})] }
	| #(LSQUARE tname:NAME
		{
            if (tables.containsKey(tname.getText())) 
            	table = tables.get(tname.getText());
			else throw new RecognitionException("Undefined table: "+ tname.getText());
		}
		( vname:NAME
			{ 
				int i = 0;
				for (AST tableEntry : table) {
					Map<String,AST>  curVars = new HashMap<String,AST> (); 
					curVars.put(vname.getText(), #(#[NUM, Integer.toString(i)]));
					res.add(new SSLInstructionName(tableEntry.getText(), curVars));
					i++;
				}
			}
		| tidx:NUM
			{
				int index = Integer.parseInt(tidx.getText());
            	if (index < table.size()) {
            		res.add(new SSLInstructionName(table.get(index).getText())); 
            	} else throw new RecognitionException("Index " + index + " out of bounds for table " + tname.getText() + "!");
			}
		))
	| d:DECOR
		{ 
			res.add(new SSLInstructionName('.' + d.getText().substring(1))); 
		}
	;


/*
 *  Expands constant, table, and function lookups.
 *  AST nodes are duplicated to avoid corruption of the AST.
 *  Returns AST objects
 */
rtl_expand
	:! #( RTL { ## = astFactory.create(RTL,"RTL"); } //#(#[RTL,"RTL"]); }
		  (rt:rtl_expand
			{
                // do not nest RTL blocks
                if (rt.getType() == RTL) {
                    if (rt.getFirstChild() != null)
                        ##.addChild(rt.getFirstChild());
                } else
                    ##.addChild(#rt);
			}
		  )*
	  )
	|! name:NAME
		{
            String s = #name.getText();
            if (locals.peek().containsKey(s))
                ## = astFactory.dupTree(locals.peek().get(s));
            else if (constants.containsKey(s))
                ## = astFactory.create(NUM, Long.toString(constants.get(s)));
            else
                ## = astFactory.dupTree(#name);
		}
	|! #(LSQUARE etname:NAME etindex:rtl_expand)
		{
            List<AST> table = tables.get(#etname.getText());
            int index = Integer.parseInt(#etindex.getText());
            AST expr = table.get(index);
            ## = astFactory.dupTree(expr);
		}
	|! #(LOOKUP_OP lexpr:rtl_expand otname:NAME otindex:rtl_expand rexpr:rtl_expand)
		{
            List <AST> table = tables.get(#otname.getText());
            int index = Integer.parseInt(#otindex.getText());
            AST op = table.get(index);
            op = astFactory.dupTree(op);
            ## = #(op, #lexpr, #rexpr);
		}
	|! #(FUNCTION fname:NAME { List<AST> fargs = new LinkedList<AST>(); } (farg:rtl_expand { fargs.add(#farg); } )* )
		{
            SSLFunction f = functions.get(fname.getText());
			Map<String,AST> assignment = new HashMap<String,AST>();
			for (int i=0; i<f.getParameterCount(); i++)
				assignment.put(f.getParameter(i), fargs.get(i));
			if (assignment != null) locals.push(assignment); else locals.push(new HashMap<String,AST>());
            rtl_expand(f.getAST());
            ## = this.getAST();
            locals.pop();
		}
	| #( . ( rtl_expand )* )
		// recurse
	;



////////////////////////////////////////////////////////////////////////////////
//   AST to RTL Converter. Called from SSL Library after initial parsing.
////////////////////////////////////////////////////////////////////////////////


convertToRTL returns [ StatementSequence statements = new StatementSequence(); ]
{ 
	RTLExpression lhs = null; 
	RTLExpression rhs = null;
	RTLExpression cnt = null; 
	StatementSequence subStatements = null;
	int bitWidth = -1;
}
	:
	/* Combine everything under an RTL node*/
	  ! #( RTL (subStatements=convertToRTL { statements.addLast(subStatements); } )* )	
	/* Almost all statements are assignments */ 
	| ! #( type:ASSIGNTYPE { 
			String aType = type.getText();
			if (aType.length() >= 3) aType = aType.substring(1, aType.length() - 1);
			else aType = "0";
			if (aType.startsWith("f")) aType = aType.substring(1); // Float assigntype
			bitWidth = Integer.parseInt(aType);
		}
		// RHS-Bitwidths are differentiated by making them negative
		lhs=rtlExpr[bitWidth] rhs=rtlExpr[-bitWidth] )
	{
		statements.addFirst(new AssignmentTemplate(bitWidth, (Writable)lhs, rhs));
		//System.out.println("Got assigntype!" + statements.toString());
	}
	| ! #( "MEMSET" { bitWidth = constants.get("ADDRESSBITS").intValue(); }
		lhs=rtlExpr[bitWidth] rhs=rtlExpr[RTLVariable.UNKNOWN_BITWIDTH] cnt=rtlExpr[bitWidth] 
		)
	{
		statements.addFirst(new RTLMemset(lhs, rhs, cnt));
	}  
	| ! #( "MEMCPY" { bitWidth = constants.get("ADDRESSBITS").intValue(); }
		lhs=rtlExpr[bitWidth] rhs=rtlExpr[bitWidth] cnt=rtlExpr[bitWidth] 
		)
	{
		statements.addFirst(new RTLMemcpy(lhs, rhs, cnt));
	}  
	/* Make FPUSH, FPOP, and anything else RTLDirectives by default */
	// | ! #(other:. (.)* ) { statements.addFirst(new RTLDirective(other.getText())); }
	// Turn it to skips. Directives were ignored all the time anyway and were only used for FPUSH and FPOP 
	| ! #(other:. (.)* ) {
		if (other.getText().equals("halt")) {
			statements.addFirst(new RTLHalt());
		} 
		else statements.addFirst(new RTLSkip()); 
	} 
;

/*		
	Missing suffix:		PRIME^ // prime suffix (whatever that means))
*/
		
convertSimplificationTemplates returns [ Map<RTLExpression,RTLExpression> mapping = new HashMap<RTLExpression,RTLExpression>()]
{
	RTLExpression lhs = null; 
	RTLExpression rhs = null;
	int bitWidth = -1;
	Map<RTLExpression,RTLExpression> subMap = null;
}
	:
	/* Combine everything under an RTL node*/
	  ! #( RTL (subMap=convertSimplificationTemplates { mapping.putAll(subMap); } )* )	
	/* Almost all statements are assignments */ 
    | ! #( type:ASSIGNTYPE lhs=rtlExpr[RTLVariable.UNKNOWN_BITWIDTH] rhs=rtlExpr[RTLVariable.UNKNOWN_BITWIDTH] ) {
		mapping.put(lhs, rhs);
	}
;


rtlExpr[int bw] returns [ RTLExpression ret = null;]
{   
	RTLExpression e1 = null, e2 = null, e3 = null;
	RTLExpression[] exprList = new RTLExpression[5]; // Needed for the BUILTIN-rule
	int i = 0; // counter 
	int n1 = -1, n2 = -1; 
	double f1 = Double.NaN;
	String str = null; 
}
	:
		// Test operators 
		#( EQ e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createEqual(e1, e2); }
		| #( NE e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createNotEqual(e1, e2); }
		| #( GT e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createGreaterThan(e1, e2); }
		| #( LT e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createLessThan(e1, e2); }
		| #( GE e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createGreaterOrEqual(e1, e2); }
		| #( LE e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createLessOrEqual(e1, e2); }
		| #( GTU e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createUnsignedGreaterThan(e1, e2); }
		| #( LTU e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createUnsignedLessThan(e1, e2); }
		| #( GEU e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createUnsignedGreaterOrEqual(e1, e2); }
		| #( LEU e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createUnsignedLessOrEqual(e1, e2); }
		// Arithmetic operators
		| #( PLUS e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createPlus(e1, e2); }
		| #( PLUS_F e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createPlus(e1, e2); }
		| #( PLUS_FD e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createPlus(e1, e2); }
		| #( PLUS_FQ e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createPlus(e1, e2); }
		| #( MINUS e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createMinus(e1, e2); }
		| #( MINUS_F e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createMinus(e1, e2); }
		| #( MINUS_FD e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createMinus(e1, e2); }
		| #( MINUS_FQ e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createMinus(e1, e2); }
		| #( MUL e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createMultiply(e1, e2); }
		| #( MUL_F e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createFloatMultiply(e1, e2); }
		| #( MUL_FD e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createFloatMultiply(e1, e2); }
		| #( MUL_FQ e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createFloatMultiply(e1, e2); }
		| #( MUL_FSD e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createFloatMultiply(e1, e2); }
		| #( MUL_FDQ e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createFloatMultiply(e1, e2); }
		| #( SMUL e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createMultiply(e1, e2); }
		| #( DIV e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createDivide(e1, e2); }
		| #( DIV_F e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createFloatDivide(e1, e2); }
		| #( DIV_FD e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createFloatDivide(e1, e2); }
		| #( DIV_FQ e1=rtlExpr[bw] e2=rtlExpr[bw]) { ret = ExpressionFactory.createFloatDivide(e1, e2); }
		| #( SDIV e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createDivide(e1, e2); }
		| #( MOD e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createModulo(e1, e2); }
		| #( SMOD e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createModulo(e1, e2); }
		| #( "pow" e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createPowerOf(e1, e2); }
		// Logcical operators
		| #( AND e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createAnd(e1, e2); }
		| #( LAND e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createAnd(e1, e2); }
		| #( OR e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createOr(e1, e2); }
		| #( LOR e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createOr(e1, e2); }
		| #( XOR e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createXor(e1, e2); }
		| #( ANDNOT e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createAnd(e1, ExpressionFactory.createNot(e2)); }
		| #( ORNOT e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createOr(e1, ExpressionFactory.createNot(e2)); }
		| #( XORNOT e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createXor(e1, ExpressionFactory.createNot(e2)); }
		| #( NOT e1=rtlExpr[bw] ) { ret = ExpressionFactory.createNot(e1); }
		| #( LNOT e1=rtlExpr[bw] ) { ret = ExpressionFactory.createNot(e1); }
		| #( FNEG e1=rtlExpr[bw] ) { ret = ExpressionFactory.createNeg(e1); }
		// Shift operators
		| #( "rlc" e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createRotateLeftWithCarry(e1, e2); }
		| #( "rrc" e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createRotateRightWithCarry(e1, e2); }
		| #( "rl" e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createRotateLeft(e1, e2); }
		| #( "rr" e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createRotateRight(e1, e2); }
		| #( RSHIFT e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createShiftRight(e1, e2); }
		| #( LSHIFT e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createShiftLeft(e1, e2); }
		| #( RSHIFTA e1=rtlExpr[bw] e2=rtlExpr[bw] ) { ret = ExpressionFactory.createShiftArithmeticRight(e1, e2); }
		// Primitives
		| vname:NAME	{ ret = ExpressionFactory.createRegisterVariable(vname.getText(), (bw>0 ? bw : RTLVariable.UNKNOWN_BITWIDTH)); }
		| rname:REG_ID	{ ret = ExpressionFactory.createRegisterVariable(rname.getText(), (bw>0 ? bw : RTLVariable.UNKNOWN_BITWIDTH)); }
		// | #( riname:REG_IDX e1=rtlExpr[bw] ) { ret = RTLVariable.valueOf(riname.getText() + "[" + e1.toString() + "]"); }
		| n1=intValue { ret = ExpressionFactory.createNumber(n1, RTLVariable.UNKNOWN_BITWIDTH); }
		// Round floats to long - not very nice :(
		| f1=floatValue { ret = ExpressionFactory.createNumber((long)f1, 80); }
		| #( MEM_IDX e1=rtlExpr[-Math.abs(bw)] ) { ret = ExpressionFactory.createMemoryLocation(e1, (bw!=0 ? Math.abs(bw) : RTLVariable.UNKNOWN_BITWIDTH)); }
		// Cast
		// this is now turned around in the parser to allow bitwidth inference - simply set bitwidth to the cast value
		| #( CAST n1=intValue e1=rtlExpr[n1] ) { 
			//ret = ExpressionFactory.createCast(e1, ExpressionFactory.createNumber(n1, RTLVariable.UNKNOWN_BITWIDTH));
			ret = e1;
			}
		// Sign Extension -- I never saw this operator (!) in use... sign extension now refers to sgnex() 
		//| #( S_E e1=rtlExpr[bw] ) { ret = ExpressionFactory.createOperation(Operator.SIGN_EXTEND, e1); }
		// Bit index - We don't know anything about the width of the operand.
		| #( AT e1=rtlExpr[0] e2=rtlExpr[0] e3=rtlExpr[0] ) { ret = ExpressionFactory.createBitRange(e1, e2, e3); }
		// Conditional
		| #( QUEST e1=rtlExpr[bw] e2=rtlExpr[bw] e3=rtlExpr[bw] ) { ret = ExpressionFactory.createConditionalExpression(e1, e2, e3); }
		// Builtin functions 
		| #( BUILTIN str=nameValue (
				 e1=rtlExpr[bw] { exprList[i++] = e1; }  
			  )* )	{
			  	if (str.equals("sgnex")) ret = ExpressionFactory.createSignExtend(exprList[0], exprList[1], exprList[2]);
			  	else if (str.equals("zfill")) ret = ExpressionFactory.createZeroFill(exprList[0], exprList[1], exprList[2]);
			  	else if (str.equals("fsize")) ret = ExpressionFactory.createFloatResize(exprList[0], exprList[1], exprList[2]);
			  	// temporary solution until real float support
			  	else if (str.equals("ftoi")) ret = ExpressionFactory.createFloatResize(exprList[0], exprList[1], exprList[2]);
			  	else if (str.equals("itof")) ret = ExpressionFactory.createFloatResize(exprList[0], exprList[1], exprList[2]);
				else ret = ExpressionFactory.createSpecialExpression(str, exprList); 
			}
;


intValue returns [ int value = -1; ]
	:	number:NUM { value = Integer.parseInt(number.getText()); }
;

floatValue returns [ double value = -1; ]
	:	number:FLOATNUM { value = Double.parseDouble(number.getText()); }
;

nameValue returns [ String value = null; ]
	:	str:NAME { value = str.getText(); }
;