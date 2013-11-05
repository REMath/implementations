// $ANTLR : "SSL.g" -> "SSLParser.java"$

	package org.jakstab.ssl.parser;

import antlr.TokenBuffer;
import antlr.TokenStreamException;
import antlr.TokenStreamIOException;
import antlr.ANTLRException;
import antlr.LLkParser;
import antlr.Token;
import antlr.TokenStream;
import antlr.RecognitionException;
import antlr.NoViableAltException;
import antlr.MismatchedTokenException;
import antlr.SemanticException;
import antlr.ParserSharedInputState;
import antlr.collections.impl.BitSet;
import antlr.collections.AST;
import java.util.Hashtable;
import antlr.ASTFactory;
import antlr.ASTPair;
import antlr.collections.impl.ASTArray;

	import java.util.*;

	@SuppressWarnings("all")

public class SSLParser extends antlr.LLkParser       implements SSLParserTokenTypes
 {

	// Begin parser

protected SSLParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
  buildTokenTypeASTClassMap();
  astFactory = new ASTFactory(getTokenTypeToASTClassMap());
}

public SSLParser(TokenBuffer tokenBuf) {
  this(tokenBuf,3);
}

protected SSLParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
  buildTokenTypeASTClassMap();
  astFactory = new ASTFactory(getTokenTypeToASTClassMap());
}

public SSLParser(TokenStream lexer) {
  this(lexer,3);
}

public SSLParser(ParserSharedInputState state) {
  super(state,3);
  tokenNames = _tokenNames;
  buildTokenTypeASTClassMap();
  astFactory = new ASTFactory(getTokenTypeToASTClassMap());
}

	public final void start() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST start_AST = null;
		
		try {      // for error handling
			specification();
			astFactory.addASTChild(currentAST, returnAST);
			match(Token.EOF_TYPE);
			start_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		returnAST = start_AST;
	}
	
	public final void specification() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST specification_AST = null;
		
		try {      // for error handling
			{
			_loop3071:
			do {
				if ((_tokenSet_1.member(LA(1)))) {
					part();
					astFactory.addASTChild(currentAST, returnAST);
					match(SEMI);
				}
				else {
					break _loop3071;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				specification_AST = (AST)currentAST.root;
				specification_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(SEMI,"SEMI")).add(specification_AST));
				currentAST.root = specification_AST;
				currentAST.child = specification_AST!=null &&specification_AST.getFirstChild()!=null ?
					specification_AST.getFirstChild() : specification_AST;
				currentAST.advanceChildToEnd();
			}
			specification_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		returnAST = specification_AST;
	}
	
	public final void part() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST part_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case LITERAL_INTEGER:
			case LITERAL_FLOAT:
			{
				registers_decl();
				astFactory.addASTChild(currentAST, returnAST);
				part_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_OPERAND:
			{
				operands_decl();
				astFactory.addASTChild(currentAST, returnAST);
				part_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_ENDIANNESS:
			{
				endianness();
				astFactory.addASTChild(currentAST, returnAST);
				part_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_FAST:
			{
				fast_list();
				astFactory.addASTChild(currentAST, returnAST);
				part_AST = (AST)currentAST.root;
				break;
			}
			default:
				if ((LA(1)==NAME) && (LA(2)==EQUATE) && (LA(3)==NUM)) {
					const_def();
					astFactory.addASTChild(currentAST, returnAST);
					part_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==NAME) && (LA(2)==LPAREN)) {
					function_def();
					astFactory.addASTChild(currentAST, returnAST);
					part_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==NAME) && (LA(2)==EQUATE) && (LA(3)==NAME||LA(3)==LCURLY)) {
					table_def();
					astFactory.addASTChild(currentAST, returnAST);
					part_AST = (AST)currentAST.root;
				}
				else if ((_tokenSet_2.member(LA(1))) && (_tokenSet_3.member(LA(2)))) {
					instr_def();
					astFactory.addASTChild(currentAST, returnAST);
					part_AST = (AST)currentAST.root;
				}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = part_AST;
	}
	
	public final void const_def() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST const_def_AST = null;
		AST v_AST = null;
		
		try {      // for error handling
			AST tmp102_AST = null;
			tmp102_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp102_AST);
			match(NAME);
			match(EQUATE);
			const_expr();
			v_AST = (AST)returnAST;
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				const_def_AST = (AST)currentAST.root;
				const_def_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CONSTANT,"CONSTANT")).add(const_def_AST));
				currentAST.root = const_def_AST;
				currentAST.child = const_def_AST!=null &&const_def_AST.getFirstChild()!=null ?
					const_def_AST.getFirstChild() : const_def_AST;
				currentAST.advanceChildToEnd();
			}
			const_def_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = const_def_AST;
	}
	
	public final void registers_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST registers_decl_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LITERAL_INTEGER:
			{
				AST tmp104_AST = null;
				tmp104_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp104_AST);
				match(LITERAL_INTEGER);
				break;
			}
			case LITERAL_FLOAT:
			{
				AST tmp105_AST = null;
				tmp105_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp105_AST);
				match(LITERAL_FLOAT);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			register_decl();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3082:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					register_decl();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3082;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				registers_decl_AST = (AST)currentAST.root;
				registers_decl_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(REGDECL,"REGDECL")).add(registers_decl_AST));
				currentAST.root = registers_decl_AST;
				currentAST.child = registers_decl_AST!=null &&registers_decl_AST.getFirstChild()!=null ?
					registers_decl_AST.getFirstChild() : registers_decl_AST;
				currentAST.advanceChildToEnd();
			}
			registers_decl_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = registers_decl_AST;
	}
	
	public final void operands_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST operands_decl_AST = null;
		
		try {      // for error handling
			AST tmp107_AST = null;
			tmp107_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp107_AST);
			match(LITERAL_OPERAND);
			operand_decl();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3091:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					operand_decl();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3091;
				}
				
			} while (true);
			}
			operands_decl_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = operands_decl_AST;
	}
	
	public final void endianness() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST endianness_AST = null;
		
		try {      // for error handling
			AST tmp109_AST = null;
			tmp109_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp109_AST);
			match(LITERAL_ENDIANNESS);
			{
			switch ( LA(1)) {
			case LITERAL_BIG:
			{
				AST tmp110_AST = null;
				tmp110_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp110_AST);
				match(LITERAL_BIG);
				break;
			}
			case LITERAL_LITTLE:
			{
				AST tmp111_AST = null;
				tmp111_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp111_AST);
				match(LITERAL_LITTLE);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			endianness_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = endianness_AST;
	}
	
	public final void function_def() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST function_def_AST = null;
		
		try {      // for error handling
			AST tmp112_AST = null;
			tmp112_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp112_AST);
			match(NAME);
			match(LPAREN);
			param_list();
			astFactory.addASTChild(currentAST, returnAST);
			match(RPAREN);
			match(LCURLY);
			rt_list();
			astFactory.addASTChild(currentAST, returnAST);
			match(RCURLY);
			if ( inputState.guessing==0 ) {
				function_def_AST = (AST)currentAST.root;
				function_def_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(FUNCTION,"FUNCTION")).add(function_def_AST));
				currentAST.root = function_def_AST;
				currentAST.child = function_def_AST!=null &&function_def_AST.getFirstChild()!=null ?
					function_def_AST.getFirstChild() : function_def_AST;
				currentAST.advanceChildToEnd();
			}
			function_def_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = function_def_AST;
	}
	
	public final void table_def() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST table_def_AST = null;
		
		try {      // for error handling
			AST tmp117_AST = null;
			tmp117_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp117_AST);
			match(NAME);
			match(EQUATE);
			table_expr();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				table_def_AST = (AST)currentAST.root;
				table_def_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(TABLE,"TABLE")).add(table_def_AST));
				currentAST.root = table_def_AST;
				currentAST.child = table_def_AST!=null &&table_def_AST.getFirstChild()!=null ?
					table_def_AST.getFirstChild() : table_def_AST;
				currentAST.advanceChildToEnd();
			}
			table_def_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = table_def_AST;
	}
	
	public final void instr_def() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST instr_def_AST = null;
		
		try {      // for error handling
			instr_name();
			astFactory.addASTChild(currentAST, returnAST);
			param_list();
			astFactory.addASTChild(currentAST, returnAST);
			rt_list();
			astFactory.addASTChild(currentAST, returnAST);
			if ( inputState.guessing==0 ) {
				instr_def_AST = (AST)currentAST.root;
				instr_def_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(INSTR,"INSTR")).add(instr_def_AST));
				currentAST.root = instr_def_AST;
				currentAST.child = instr_def_AST!=null &&instr_def_AST.getFirstChild()!=null ?
					instr_def_AST.getFirstChild() : instr_def_AST;
				currentAST.advanceChildToEnd();
			}
			instr_def_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = instr_def_AST;
	}
	
	public final void fast_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST fast_list_AST = null;
		
		try {      // for error handling
			AST tmp119_AST = null;
			tmp119_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp119_AST);
			match(LITERAL_FAST);
			fast_entry();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3190:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					fast_entry();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3190;
				}
				
			} while (true);
			}
			fast_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = fast_list_AST;
	}
	
	public final void num() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST num_AST = null;
		
		try {      // for error handling
			AST tmp121_AST = null;
			tmp121_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp121_AST);
			match(NUM);
			num_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
		returnAST = num_AST;
	}
	
	public final void const_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST const_expr_AST = null;
		
		try {      // for error handling
			AST tmp122_AST = null;
			tmp122_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp122_AST);
			match(NUM);
			{
			_loop3078:
			do {
				if ((LA(1)==PLUS||LA(1)==MINUS)) {
					{
					switch ( LA(1)) {
					case PLUS:
					{
						AST tmp123_AST = null;
						tmp123_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp123_AST);
						match(PLUS);
						break;
					}
					case MINUS:
					{
						AST tmp124_AST = null;
						tmp124_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp124_AST);
						match(MINUS);
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					AST tmp125_AST = null;
					tmp125_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp125_AST);
					match(NUM);
				}
				else {
					break _loop3078;
				}
				
			} while (true);
			}
			const_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = const_expr_AST;
	}
	
	public final void register_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST register_decl_AST = null;
		
		try {      // for error handling
			if ((LA(1)==REG_ID) && (LA(2)==INDEX)) {
				AST tmp126_AST = null;
				tmp126_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp126_AST);
				match(REG_ID);
				AST tmp127_AST = null;
				tmp127_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp127_AST);
				match(INDEX);
				num();
				astFactory.addASTChild(currentAST, returnAST);
				register_decl_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==REG_ID) && (LA(2)==LSQUARE)) {
				AST tmp128_AST = null;
				tmp128_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp128_AST);
				match(REG_ID);
				AST tmp129_AST = null;
				tmp129_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp129_AST);
				match(LSQUARE);
				num();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp130_AST = null;
				tmp130_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp130_AST);
				match(RSQUARE);
				AST tmp131_AST = null;
				tmp131_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp131_AST);
				match(INDEX);
				num();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case LITERAL_COVERS:
				{
					AST tmp132_AST = null;
					tmp132_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp132_AST);
					match(LITERAL_COVERS);
					AST tmp133_AST = null;
					tmp133_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp133_AST);
					match(REG_ID);
					AST tmp134_AST = null;
					tmp134_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp134_AST);
					match(TO);
					AST tmp135_AST = null;
					tmp135_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp135_AST);
					match(REG_ID);
					break;
				}
				case LITERAL_SHARES:
				{
					AST tmp136_AST = null;
					tmp136_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp136_AST);
					match(LITERAL_SHARES);
					AST tmp137_AST = null;
					tmp137_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp137_AST);
					match(REG_ID);
					AST tmp138_AST = null;
					tmp138_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp138_AST);
					match(AT);
					AST tmp139_AST = null;
					tmp139_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp139_AST);
					match(LSQUARE);
					num();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp140_AST = null;
					tmp140_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp140_AST);
					match(TO);
					num();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp141_AST = null;
					tmp141_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp141_AST);
					match(RSQUARE);
					break;
				}
				case SEMI:
				case COMMA:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				register_decl_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==LSQUARE)) {
				AST tmp142_AST = null;
				tmp142_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp142_AST);
				match(LSQUARE);
				register_list();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp143_AST = null;
				tmp143_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp143_AST);
				match(RSQUARE);
				AST tmp144_AST = null;
				tmp144_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp144_AST);
				match(LSQUARE);
				num();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp145_AST = null;
				tmp145_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp145_AST);
				match(RSQUARE);
				AST tmp146_AST = null;
				tmp146_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp146_AST);
				match(INDEX);
				num();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case TO:
				{
					AST tmp147_AST = null;
					tmp147_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp147_AST);
					match(TO);
					num();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case SEMI:
				case COMMA:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				register_decl_AST = (AST)currentAST.root;
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		returnAST = register_decl_AST;
	}
	
	public final void register_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST register_list_AST = null;
		
		try {      // for error handling
			AST tmp148_AST = null;
			tmp148_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp148_AST);
			match(REG_ID);
			{
			_loop3088:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					AST tmp150_AST = null;
					tmp150_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp150_AST);
					match(REG_ID);
				}
				else {
					break _loop3088;
				}
				
			} while (true);
			}
			register_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_7);
			} else {
			  throw ex;
			}
		}
		returnAST = register_list_AST;
	}
	
	public final void operand_decl() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST operand_decl_AST = null;
		
		try {      // for error handling
			if ((LA(1)==NAME) && (LA(2)==EQUATE)) {
				AST tmp151_AST = null;
				tmp151_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp151_AST);
				match(NAME);
				AST tmp152_AST = null;
				tmp152_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp152_AST);
				match(EQUATE);
				match(LCURLY);
				param_list();
				astFactory.addASTChild(currentAST, returnAST);
				match(RCURLY);
				operand_decl_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==NAME) && (LA(2)==NAME||LA(2)==LSQUARE||LA(2)==ASSIGNTYPE)) {
				AST tmp155_AST = null;
				tmp155_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp155_AST);
				match(NAME);
				param_list();
				astFactory.addASTChild(currentAST, returnAST);
				{
				switch ( LA(1)) {
				case LSQUARE:
				{
					AST tmp156_AST = null;
					tmp156_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp156_AST);
					match(LSQUARE);
					param_list();
					astFactory.addASTChild(currentAST, returnAST);
					AST tmp157_AST = null;
					tmp157_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp157_AST);
					match(RSQUARE);
					break;
				}
				case ASSIGNTYPE:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				AST tmp158_AST = null;
				tmp158_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp158_AST);
				match(ASSIGNTYPE);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				operand_decl_AST = (AST)currentAST.root;
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		returnAST = operand_decl_AST;
	}
	
	public final void param_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST param_list_AST = null;
		Token  t = null;
		AST t_AST = null;
		
		try {      // for error handling
			{
			boolean synPredMatched3138 = false;
			if (((LA(1)==NAME) && (_tokenSet_8.member(LA(2))) && (_tokenSet_9.member(LA(3))))) {
				int _m3138 = mark();
				synPredMatched3138 = true;
				inputState.guessing++;
				try {
					{
					match(NAME);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched3138 = false;
				}
				rewind(_m3138);
inputState.guessing--;
			}
			if ( synPredMatched3138 ) {
				AST tmp159_AST = null;
				tmp159_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp159_AST);
				match(NAME);
				{
				_loop3140:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						t = LT(1);
						t_AST = astFactory.create(t);
						astFactory.addASTChild(currentAST, t_AST);
						match(NAME);
					}
					else {
						break _loop3140;
					}
					
				} while (true);
				}
			}
			else if ((_tokenSet_10.member(LA(1))) && (_tokenSet_9.member(LA(2))) && (_tokenSet_11.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			if ( inputState.guessing==0 ) {
				param_list_AST = (AST)currentAST.root;
				param_list_AST = (AST)astFactory.make( (new ASTArray(2)).add((AST)astFactory.create(COMMA,",")).add(param_list_AST));
				currentAST.root = param_list_AST;
				currentAST.child = param_list_AST!=null &&param_list_AST.getFirstChild()!=null ?
					param_list_AST.getFirstChild() : param_list_AST;
				currentAST.advanceChildToEnd();
			}
			param_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_10);
			} else {
			  throw ex;
			}
		}
		returnAST = param_list_AST;
	}
	
	public final void expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST expr_AST = null;
		
		try {      // for error handling
			log_expr();
			astFactory.addASTChild(currentAST, returnAST);
			expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_12);
			} else {
			  throw ex;
			}
		}
		returnAST = expr_AST;
	}
	
	public final void rt_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST rt_list_AST = null;
		
		try {      // for error handling
			{
			int _cnt3133=0;
			_loop3133:
			do {
				if ((_tokenSet_13.member(LA(1)))) {
					rt();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					if ( _cnt3133>=1 ) { break _loop3133; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt3133++;
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				rt_list_AST = (AST)currentAST.root;
				rt_list_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(RTL,"RTL")).add(rt_list_AST));
				currentAST.root = rt_list_AST;
				currentAST.child = rt_list_AST!=null &&rt_list_AST.getFirstChild()!=null ?
					rt_list_AST.getFirstChild() : rt_list_AST;
				currentAST.advanceChildToEnd();
			}
			rt_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_14);
			} else {
			  throw ex;
			}
		}
		returnAST = rt_list_AST;
	}
	
	public final void table_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST table_expr_AST = null;
		
		try {      // for error handling
			boolean synPredMatched3100 = false;
			if (((LA(1)==NAME||LA(1)==LCURLY) && (_tokenSet_15.member(LA(2))) && (_tokenSet_16.member(LA(3))))) {
				int _m3100 = mark();
				synPredMatched3100 = true;
				inputState.guessing++;
				try {
					{
					str_table_expr();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched3100 = false;
				}
				rewind(_m3100);
inputState.guessing--;
			}
			if ( synPredMatched3100 ) {
				str_table_expr();
				astFactory.addASTChild(currentAST, returnAST);
				table_expr_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==LCURLY) && (LA(2)==QUOTE) && (_tokenSet_17.member(LA(3)))) {
				op_str_table();
				astFactory.addASTChild(currentAST, returnAST);
				table_expr_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==LCURLY) && (LA(2)==QUOTE) && (_tokenSet_18.member(LA(3)))) {
				expr_str_table();
				astFactory.addASTChild(currentAST, returnAST);
				table_expr_AST = (AST)currentAST.root;
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = table_expr_AST;
	}
	
	public final void str_table_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST str_table_expr_AST = null;
		
		try {      // for error handling
			str_table();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3103:
			do {
				if ((LA(1)==NAME||LA(1)==LCURLY)) {
					str_table();
					astFactory.addASTChild(currentAST, returnAST);
					if ( inputState.guessing==0 ) {
						str_table_expr_AST = (AST)currentAST.root;
						str_table_expr_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(CROSSP,"CROSSP")).add(str_table_expr_AST));
						currentAST.root = str_table_expr_AST;
						currentAST.child = str_table_expr_AST!=null &&str_table_expr_AST.getFirstChild()!=null ?
							str_table_expr_AST.getFirstChild() : str_table_expr_AST;
						currentAST.advanceChildToEnd();
					}
				}
				else {
					break _loop3103;
				}
				
			} while (true);
			}
			str_table_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = str_table_expr_AST;
	}
	
	public final void op_str_table() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST op_str_table_AST = null;
		AST t_AST = null;
		
		try {      // for error handling
			AST tmp161_AST = null;
			tmp161_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp161_AST);
			match(LCURLY);
			op_str_entry();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3110:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					op_str_entry();
					t_AST = (AST)returnAST;
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3110;
				}
				
			} while (true);
			}
			match(RCURLY);
			op_str_table_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = op_str_table_AST;
	}
	
	public final void expr_str_table() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST expr_str_table_AST = null;
		AST t_AST = null;
		
		try {      // for error handling
			AST tmp164_AST = null;
			tmp164_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp164_AST);
			match(LCURLY);
			expr_str_entry();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3115:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					expr_str_entry();
					t_AST = (AST)returnAST;
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3115;
				}
				
			} while (true);
			}
			match(RCURLY);
			expr_str_table_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		returnAST = expr_str_table_AST;
	}
	
	public final void str_table() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST str_table_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case NAME:
			{
				AST tmp167_AST = null;
				tmp167_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp167_AST);
				match(NAME);
				str_table_AST = (AST)currentAST.root;
				break;
			}
			case LCURLY:
			{
				AST tmp168_AST = null;
				tmp168_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp168_AST);
				match(LCURLY);
				str_entry();
				astFactory.addASTChild(currentAST, returnAST);
				{
				_loop3106:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						str_entry();
						astFactory.addASTChild(currentAST, returnAST);
					}
					else {
						break _loop3106;
					}
					
				} while (true);
				}
				match(RCURLY);
				str_table_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_19);
			} else {
			  throw ex;
			}
		}
		returnAST = str_table_AST;
	}
	
	public final void str_entry() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST str_entry_AST = null;
		
		try {      // for error handling
			if ((LA(1)==NAME)) {
				AST tmp171_AST = null;
				tmp171_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp171_AST);
				match(NAME);
				str_entry_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==QUOTE) && (LA(2)==QUOTE)) {
				AST tmp172_AST = null;
				tmp172_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp172_AST);
				match(QUOTE);
				match(QUOTE);
				if ( inputState.guessing==0 ) {
					str_entry_AST = (AST)currentAST.root;
					str_entry_AST = (AST)astFactory.make( (new ASTArray(2)).add(str_entry_AST).add(astFactory.create(NAME,"")));
					currentAST.root = str_entry_AST;
					currentAST.child = str_entry_AST!=null &&str_entry_AST.getFirstChild()!=null ?
						str_entry_AST.getFirstChild() : str_entry_AST;
					currentAST.advanceChildToEnd();
				}
				str_entry_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==QUOTE) && (LA(2)==NAME)) {
				AST tmp174_AST = null;
				tmp174_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp174_AST);
				match(QUOTE);
				AST tmp175_AST = null;
				tmp175_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp175_AST);
				match(NAME);
				match(QUOTE);
				str_entry_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==QUOTE) && (LA(2)==DECOR)) {
				AST tmp177_AST = null;
				tmp177_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp177_AST);
				match(QUOTE);
				AST tmp178_AST = null;
				tmp178_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp178_AST);
				match(DECOR);
				match(QUOTE);
				str_entry_AST = (AST)currentAST.root;
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_20);
			} else {
			  throw ex;
			}
		}
		returnAST = str_entry_AST;
	}
	
	public final void op_str_entry() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST op_str_entry_AST = null;
		
		try {      // for error handling
			AST tmp180_AST = null;
			tmp180_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp180_AST);
			match(QUOTE);
			bin_oper();
			astFactory.addASTChild(currentAST, returnAST);
			match(QUOTE);
			op_str_entry_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_20);
			} else {
			  throw ex;
			}
		}
		returnAST = op_str_entry_AST;
	}
	
	public final void bin_oper() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST bin_oper_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case MOD:
			{
				AST tmp182_AST = null;
				tmp182_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp182_AST);
				match(MOD);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MUL:
			{
				AST tmp183_AST = null;
				tmp183_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp183_AST);
				match(MUL);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case DIV:
			{
				AST tmp184_AST = null;
				tmp184_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp184_AST);
				match(DIV);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case SMUL:
			{
				AST tmp185_AST = null;
				tmp185_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp185_AST);
				match(SMUL);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case SDIV:
			{
				AST tmp186_AST = null;
				tmp186_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp186_AST);
				match(SDIV);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case SMOD:
			{
				AST tmp187_AST = null;
				tmp187_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp187_AST);
				match(SMOD);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case PLUS:
			{
				AST tmp188_AST = null;
				tmp188_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp188_AST);
				match(PLUS);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MINUS:
			{
				AST tmp189_AST = null;
				tmp189_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp189_AST);
				match(MINUS);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_rlc:
			{
				AST tmp190_AST = null;
				tmp190_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp190_AST);
				match(LITERAL_rlc);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_rrc:
			{
				AST tmp191_AST = null;
				tmp191_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp191_AST);
				match(LITERAL_rrc);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_rl:
			{
				AST tmp192_AST = null;
				tmp192_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp192_AST);
				match(LITERAL_rl);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_rr:
			{
				AST tmp193_AST = null;
				tmp193_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp193_AST);
				match(LITERAL_rr);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case RSHIFT:
			{
				AST tmp194_AST = null;
				tmp194_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp194_AST);
				match(RSHIFT);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LSHIFT:
			{
				AST tmp195_AST = null;
				tmp195_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp195_AST);
				match(LSHIFT);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case RSHIFTA:
			{
				AST tmp196_AST = null;
				tmp196_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp196_AST);
				match(RSHIFTA);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case OR:
			{
				AST tmp197_AST = null;
				tmp197_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp197_AST);
				match(OR);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case ORNOT:
			{
				AST tmp198_AST = null;
				tmp198_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp198_AST);
				match(ORNOT);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case AND:
			{
				AST tmp199_AST = null;
				tmp199_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp199_AST);
				match(AND);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case ANDNOT:
			{
				AST tmp200_AST = null;
				tmp200_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp200_AST);
				match(ANDNOT);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case XOR:
			{
				AST tmp201_AST = null;
				tmp201_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp201_AST);
				match(XOR);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case XORNOT:
			{
				AST tmp202_AST = null;
				tmp202_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp202_AST);
				match(XORNOT);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MUL_F:
			{
				AST tmp203_AST = null;
				tmp203_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp203_AST);
				match(MUL_F);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MUL_FD:
			{
				AST tmp204_AST = null;
				tmp204_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp204_AST);
				match(MUL_FD);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MUL_FQ:
			{
				AST tmp205_AST = null;
				tmp205_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp205_AST);
				match(MUL_FQ);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MUL_FSD:
			{
				AST tmp206_AST = null;
				tmp206_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp206_AST);
				match(MUL_FSD);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MUL_FDQ:
			{
				AST tmp207_AST = null;
				tmp207_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp207_AST);
				match(MUL_FDQ);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case DIV_F:
			{
				AST tmp208_AST = null;
				tmp208_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp208_AST);
				match(DIV_F);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case DIV_FD:
			{
				AST tmp209_AST = null;
				tmp209_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp209_AST);
				match(DIV_FD);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case DIV_FQ:
			{
				AST tmp210_AST = null;
				tmp210_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp210_AST);
				match(DIV_FQ);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case PLUS_F:
			{
				AST tmp211_AST = null;
				tmp211_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp211_AST);
				match(PLUS_F);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case PLUS_FD:
			{
				AST tmp212_AST = null;
				tmp212_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp212_AST);
				match(PLUS_FD);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case PLUS_FQ:
			{
				AST tmp213_AST = null;
				tmp213_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp213_AST);
				match(PLUS_FQ);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MINUS_F:
			{
				AST tmp214_AST = null;
				tmp214_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp214_AST);
				match(MINUS_F);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MINUS_FD:
			{
				AST tmp215_AST = null;
				tmp215_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp215_AST);
				match(MINUS_FD);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case MINUS_FQ:
			{
				AST tmp216_AST = null;
				tmp216_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp216_AST);
				match(MINUS_FQ);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_pow:
			{
				AST tmp217_AST = null;
				tmp217_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp217_AST);
				match(LITERAL_pow);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case EQ:
			{
				AST tmp218_AST = null;
				tmp218_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp218_AST);
				match(EQ);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case NE:
			{
				AST tmp219_AST = null;
				tmp219_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp219_AST);
				match(NE);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LT:
			{
				AST tmp220_AST = null;
				tmp220_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp220_AST);
				match(LT);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case GT:
			{
				AST tmp221_AST = null;
				tmp221_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp221_AST);
				match(GT);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LE:
			{
				AST tmp222_AST = null;
				tmp222_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp222_AST);
				match(LE);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case GE:
			{
				AST tmp223_AST = null;
				tmp223_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp223_AST);
				match(GE);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LTU:
			{
				AST tmp224_AST = null;
				tmp224_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp224_AST);
				match(LTU);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case GTU:
			{
				AST tmp225_AST = null;
				tmp225_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp225_AST);
				match(GTU);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case LEU:
			{
				AST tmp226_AST = null;
				tmp226_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp226_AST);
				match(LEU);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			case GEU:
			{
				AST tmp227_AST = null;
				tmp227_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp227_AST);
				match(GEU);
				bin_oper_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
		returnAST = bin_oper_AST;
	}
	
	public final void expr_str_entry() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST expr_str_entry_AST = null;
		
		try {      // for error handling
			AST tmp228_AST = null;
			tmp228_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp228_AST);
			match(QUOTE);
			expr();
			astFactory.addASTChild(currentAST, returnAST);
			match(QUOTE);
			expr_str_entry_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_20);
			} else {
			  throw ex;
			}
		}
		returnAST = expr_str_entry_AST;
	}
	
	public final void instr_name() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST instr_name_AST = null;
		
		try {      // for error handling
			instr_name_head();
			astFactory.addASTChild(currentAST, returnAST);
			instr_name_tail();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3120:
			do {
				if ((LA(1)==DECOR)) {
					instr_name_decor();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3120;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				instr_name_AST = (AST)currentAST.root;
				instr_name_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(INSTR_NAME,"INSTR_NAME")).add(instr_name_AST));
				currentAST.root = instr_name_AST;
				currentAST.child = instr_name_AST!=null &&instr_name_AST.getFirstChild()!=null ?
					instr_name_AST.getFirstChild() : instr_name_AST;
				currentAST.advanceChildToEnd();
			}
			instr_name_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		returnAST = instr_name_AST;
	}
	
	public final void instr_name_head() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST instr_name_head_AST = null;
		
		try {      // for error handling
			boolean synPredMatched3123 = false;
			if (((_tokenSet_2.member(LA(1))) && (LA(2)==NAME||LA(2)==LSQUARE) && (_tokenSet_22.member(LA(3))))) {
				int _m3123 = mark();
				synPredMatched3123 = true;
				inputState.guessing++;
				try {
					{
					instr_name_elem();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched3123 = false;
				}
				rewind(_m3123);
inputState.guessing--;
			}
			if ( synPredMatched3123 ) {
				instr_name_elem();
				astFactory.addASTChild(currentAST, returnAST);
				instr_name_tail();
				astFactory.addASTChild(currentAST, returnAST);
				instr_name_head_AST = (AST)currentAST.root;
			}
			else if ((LA(1)==NAME) && (_tokenSet_23.member(LA(2))) && (_tokenSet_24.member(LA(3)))) {
				AST tmp230_AST = null;
				tmp230_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp230_AST);
				match(NAME);
				instr_name_head_AST = (AST)currentAST.root;
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
		returnAST = instr_name_head_AST;
	}
	
	public final void instr_name_tail() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST instr_name_tail_AST = null;
		
		try {      // for error handling
			boolean synPredMatched3129 = false;
			if (((_tokenSet_2.member(LA(1))) && (LA(2)==NAME||LA(2)==LSQUARE) && (_tokenSet_22.member(LA(3))))) {
				int _m3129 = mark();
				synPredMatched3129 = true;
				inputState.guessing++;
				try {
					{
					instr_name_elem();
					}
				}
				catch (RecognitionException pe) {
					synPredMatched3129 = false;
				}
				rewind(_m3129);
inputState.guessing--;
			}
			if ( synPredMatched3129 ) {
				instr_name_elem();
				astFactory.addASTChild(currentAST, returnAST);
				instr_name_tail();
				astFactory.addASTChild(currentAST, returnAST);
				instr_name_tail_AST = (AST)currentAST.root;
			}
			else if ((_tokenSet_23.member(LA(1))) && (_tokenSet_24.member(LA(2))) && (_tokenSet_25.member(LA(3)))) {
				instr_name_tail_AST = (AST)currentAST.root;
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
		returnAST = instr_name_tail_AST;
	}
	
	public final void instr_name_decor() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST instr_name_decor_AST = null;
		
		try {      // for error handling
			AST tmp231_AST = null;
			tmp231_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp231_AST);
			match(DECOR);
			instr_name_decor_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_26);
			} else {
			  throw ex;
			}
		}
		returnAST = instr_name_decor_AST;
	}
	
	public final void instr_name_elem() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST instr_name_elem_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case PRIME:
			{
				AST tmp232_AST = null;
				tmp232_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp232_AST);
				match(PRIME);
				AST tmp233_AST = null;
				tmp233_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp233_AST);
				match(NAME);
				match(PRIME);
				instr_name_elem_AST = (AST)currentAST.root;
				break;
			}
			case QUOTE:
			{
				match(QUOTE);
				AST tmp236_AST = null;
				tmp236_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp236_AST);
				match(NAME);
				match(QUOTE);
				instr_name_elem_AST = (AST)currentAST.root;
				break;
			}
			case NAME:
			{
				AST tmp238_AST = null;
				tmp238_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp238_AST);
				match(NAME);
				AST tmp239_AST = null;
				tmp239_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp239_AST);
				match(LSQUARE);
				{
				switch ( LA(1)) {
				case NUM:
				{
					num();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case NAME:
				{
					AST tmp240_AST = null;
					tmp240_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp240_AST);
					match(NAME);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				match(RSQUARE);
				instr_name_elem_AST = (AST)currentAST.root;
				break;
			}
			case DOLLAR:
			{
				match(DOLLAR);
				AST tmp243_AST = null;
				tmp243_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp243_AST);
				match(NAME);
				AST tmp244_AST = null;
				tmp244_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp244_AST);
				match(LSQUARE);
				{
				switch ( LA(1)) {
				case NUM:
				{
					num();
					astFactory.addASTChild(currentAST, returnAST);
					break;
				}
				case NAME:
				{
					AST tmp245_AST = null;
					tmp245_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp245_AST);
					match(NAME);
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				match(RSQUARE);
				instr_name_elem_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
		returnAST = instr_name_elem_AST;
	}
	
	public final void rt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST rt_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case ASSIGNTYPE:
			case LITERAL_MEMSET:
			case LITERAL_MEMCPY:
			{
				assign_rt();
				astFactory.addASTChild(currentAST, returnAST);
				rt_AST = (AST)currentAST.root;
				break;
			}
			case NAME:
			{
				AST tmp247_AST = null;
				tmp247_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp247_AST);
				match(NAME);
				match(LPAREN);
				expr_list();
				astFactory.addASTChild(currentAST, returnAST);
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					rt_AST = (AST)currentAST.root;
					rt_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(FUNCTION,"FUNCTION")).add(rt_AST));
					currentAST.root = rt_AST;
					currentAST.child = rt_AST!=null &&rt_AST.getFirstChild()!=null ?
						rt_AST.getFirstChild() : rt_AST;
					currentAST.advanceChildToEnd();
				}
				rt_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_halt:
			{
				AST tmp250_AST = null;
				tmp250_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp250_AST);
				match(LITERAL_halt);
				rt_AST = (AST)currentAST.root;
				break;
			}
			case UNDERSCORE:
			{
				match(UNDERSCORE);
				rt_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_27);
			} else {
			  throw ex;
			}
		}
		returnAST = rt_AST;
	}
	
	public final void assign_rt() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST assign_rt_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case ASSIGNTYPE:
			{
				AST tmp252_AST = null;
				tmp252_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp252_AST);
				match(ASSIGNTYPE);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(EQUATE);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				assign_rt_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_MEMSET:
			{
				AST tmp254_AST = null;
				tmp254_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp254_AST);
				match(LITERAL_MEMSET);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(COMMA);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(COMMA);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				assign_rt_AST = (AST)currentAST.root;
				break;
			}
			case LITERAL_MEMCPY:
			{
				AST tmp257_AST = null;
				tmp257_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp257_AST);
				match(LITERAL_MEMCPY);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(COMMA);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(COMMA);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				assign_rt_AST = (AST)currentAST.root;
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_27);
			} else {
			  throw ex;
			}
		}
		returnAST = assign_rt_AST;
	}
	
	public final void expr_list() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST expr_list_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case NUM:
			case NAME:
			case REG_ID:
			case LSQUARE:
			case LPAREN:
			case REG_IDX:
			case MEM_IDX:
			case FLOATNUM:
			case NOT:
			case FNEG:
			case LNOT:
			{
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				{
				_loop3187:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						expr();
						astFactory.addASTChild(currentAST, returnAST);
					}
					else {
						break _loop3187;
					}
					
				} while (true);
				}
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			expr_list_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_28);
			} else {
			  throw ex;
			}
		}
		returnAST = expr_list_AST;
	}
	
	public final void var() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST var_AST = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case REG_ID:
			{
				AST tmp261_AST = null;
				tmp261_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp261_AST);
				match(REG_ID);
				break;
			}
			case REG_IDX:
			{
				AST tmp262_AST = null;
				tmp262_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp262_AST);
				match(REG_IDX);
				match(LSQUARE);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(RSQUARE);
				break;
			}
			case MEM_IDX:
			{
				AST tmp265_AST = null;
				tmp265_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp265_AST);
				match(MEM_IDX);
				match(LSQUARE);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(RSQUARE);
				break;
			}
			case NAME:
			{
				AST tmp268_AST = null;
				tmp268_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp268_AST);
				match(NAME);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			_loop3145:
			do {
				switch ( LA(1)) {
				case AT:
				{
					AST tmp269_AST = null;
					tmp269_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp269_AST);
					match(AT);
					match(LSQUARE);
					expr();
					astFactory.addASTChild(currentAST, returnAST);
					match(COLON);
					expr();
					astFactory.addASTChild(currentAST, returnAST);
					match(RSQUARE);
					break;
				}
				case PRIME:
				{
					AST tmp273_AST = null;
					tmp273_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp273_AST);
					match(PRIME);
					break;
				}
				default:
				{
					break _loop3145;
				}
				}
			} while (true);
			}
			var_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		returnAST = var_AST;
	}
	
	public final void primary_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST primary_expr_AST = null;
		
		try {      // for error handling
			switch ( LA(1)) {
			case NUM:
			{
				AST tmp274_AST = null;
				tmp274_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp274_AST);
				match(NUM);
				primary_expr_AST = (AST)currentAST.root;
				break;
			}
			case FLOATNUM:
			{
				AST tmp275_AST = null;
				tmp275_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp275_AST);
				match(FLOATNUM);
				primary_expr_AST = (AST)currentAST.root;
				break;
			}
			case REG_ID:
			{
				AST tmp276_AST = null;
				tmp276_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp276_AST);
				match(REG_ID);
				primary_expr_AST = (AST)currentAST.root;
				break;
			}
			case REG_IDX:
			{
				AST tmp277_AST = null;
				tmp277_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp277_AST);
				match(REG_IDX);
				match(LSQUARE);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(RSQUARE);
				primary_expr_AST = (AST)currentAST.root;
				break;
			}
			case MEM_IDX:
			{
				AST tmp280_AST = null;
				tmp280_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp280_AST);
				match(MEM_IDX);
				match(LSQUARE);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(RSQUARE);
				primary_expr_AST = (AST)currentAST.root;
				break;
			}
			case LPAREN:
			{
				match(LPAREN);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(RPAREN);
				primary_expr_AST = (AST)currentAST.root;
				break;
			}
			case LSQUARE:
			{
				match(LSQUARE);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				AST tmp286_AST = null;
				tmp286_AST = astFactory.create(LT(1));
				astFactory.makeASTRoot(currentAST, tmp286_AST);
				match(QUEST);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(COLON);
				expr();
				astFactory.addASTChild(currentAST, returnAST);
				match(RSQUARE);
				primary_expr_AST = (AST)currentAST.root;
				break;
			}
			default:
				if ((LA(1)==NAME) && (_tokenSet_29.member(LA(2)))) {
					AST tmp289_AST = null;
					tmp289_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp289_AST);
					match(NAME);
					primary_expr_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==NAME) && (LA(2)==LSQUARE)) {
					AST tmp290_AST = null;
					tmp290_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp290_AST);
					match(NAME);
					AST tmp291_AST = null;
					tmp291_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp291_AST);
					match(LSQUARE);
					{
					switch ( LA(1)) {
					case NAME:
					{
						AST tmp292_AST = null;
						tmp292_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp292_AST);
						match(NAME);
						break;
					}
					case NUM:
					{
						AST tmp293_AST = null;
						tmp293_AST = astFactory.create(LT(1));
						astFactory.addASTChild(currentAST, tmp293_AST);
						match(NUM);
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					match(RSQUARE);
					primary_expr_AST = (AST)currentAST.root;
				}
				else if ((LA(1)==NAME) && (LA(2)==LPAREN)) {
					AST tmp295_AST = null;
					tmp295_AST = astFactory.create(LT(1));
					astFactory.addASTChild(currentAST, tmp295_AST);
					match(NAME);
					match(LPAREN);
					expr_list();
					astFactory.addASTChild(currentAST, returnAST);
					match(RPAREN);
					if ( inputState.guessing==0 ) {
						primary_expr_AST = (AST)currentAST.root;
						primary_expr_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(BUILTIN,"BUILTIN")).add(primary_expr_AST));
						currentAST.root = primary_expr_AST;
						currentAST.child = primary_expr_AST!=null &&primary_expr_AST.getFirstChild()!=null ?
							primary_expr_AST.getFirstChild() : primary_expr_AST;
						currentAST.advanceChildToEnd();
					}
					primary_expr_AST = (AST)currentAST.root;
				}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_29);
			} else {
			  throw ex;
			}
		}
		returnAST = primary_expr_AST;
	}
	
	public final void postfix_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST postfix_expr_AST = null;
		AST primary_AST = null;
		AST width_AST = null;
		
		try {      // for error handling
			primary_expr();
			primary_AST = (AST)returnAST;
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3155:
			do {
				switch ( LA(1)) {
				case AT:
				{
					AST tmp298_AST = null;
					tmp298_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp298_AST);
					match(AT);
					match(LSQUARE);
					expr();
					astFactory.addASTChild(currentAST, returnAST);
					match(COLON);
					expr();
					astFactory.addASTChild(currentAST, returnAST);
					match(RSQUARE);
					break;
				}
				case S_E:
				{
					AST tmp302_AST = null;
					tmp302_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp302_AST);
					match(S_E);
					break;
				}
				case LCURLY:
				{
					{
					AST tmp303_AST = null;
					tmp303_AST = astFactory.create(LT(1));
					match(LCURLY);
					num();
					width_AST = (AST)returnAST;
					AST tmp304_AST = null;
					tmp304_AST = astFactory.create(LT(1));
					match(RCURLY);
					}
					if ( inputState.guessing==0 ) {
						postfix_expr_AST = (AST)currentAST.root;
						postfix_expr_AST = (AST)astFactory.make( (new ASTArray(3)).add(astFactory.create(CAST,"CAST")).add(width_AST).add(postfix_expr_AST));
						currentAST.root = postfix_expr_AST;
						currentAST.child = postfix_expr_AST!=null &&postfix_expr_AST.getFirstChild()!=null ?
							postfix_expr_AST.getFirstChild() : postfix_expr_AST;
						currentAST.advanceChildToEnd();
					}
					break;
				}
				default:
				{
					break _loop3155;
				}
				}
			} while (true);
			}
			postfix_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_30);
			} else {
			  throw ex;
			}
		}
		returnAST = postfix_expr_AST;
	}
	
	public final void lookup_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST lookup_expr_AST = null;
		
		try {      // for error handling
			postfix_expr();
			astFactory.addASTChild(currentAST, returnAST);
			{
			boolean synPredMatched3159 = false;
			if (((LA(1)==NAME) && (LA(2)==LSQUARE) && (LA(3)==NAME))) {
				int _m3159 = mark();
				synPredMatched3159 = true;
				inputState.guessing++;
				try {
					{
					match(NAME);
					match(LSQUARE);
					match(NAME);
					match(RSQUARE);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched3159 = false;
				}
				rewind(_m3159);
inputState.guessing--;
			}
			if ( synPredMatched3159 ) {
				AST tmp305_AST = null;
				tmp305_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp305_AST);
				match(NAME);
				match(LSQUARE);
				AST tmp307_AST = null;
				tmp307_AST = astFactory.create(LT(1));
				astFactory.addASTChild(currentAST, tmp307_AST);
				match(NAME);
				match(RSQUARE);
				lookup_expr();
				astFactory.addASTChild(currentAST, returnAST);
				if ( inputState.guessing==0 ) {
					lookup_expr_AST = (AST)currentAST.root;
					lookup_expr_AST = (AST)astFactory.make( (new ASTArray(2)).add(astFactory.create(LOOKUP_OP,"LOOKUP_OP")).add(lookup_expr_AST));
					currentAST.root = lookup_expr_AST;
					currentAST.child = lookup_expr_AST!=null &&lookup_expr_AST.getFirstChild()!=null ?
						lookup_expr_AST.getFirstChild() : lookup_expr_AST;
					currentAST.advanceChildToEnd();
				}
			}
			else if ((_tokenSet_30.member(LA(1))) && (_tokenSet_31.member(LA(2))) && (_tokenSet_32.member(LA(3)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			lookup_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_30);
			} else {
			  throw ex;
			}
		}
		returnAST = lookup_expr_AST;
	}
	
	public final void unary_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST unary_expr_AST = null;
		
		try {      // for error handling
			{
			_loop3162:
			do {
				switch ( LA(1)) {
				case NOT:
				{
					AST tmp309_AST = null;
					tmp309_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp309_AST);
					match(NOT);
					break;
				}
				case FNEG:
				{
					AST tmp310_AST = null;
					tmp310_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp310_AST);
					match(FNEG);
					break;
				}
				case LNOT:
				{
					AST tmp311_AST = null;
					tmp311_AST = astFactory.create(LT(1));
					astFactory.makeASTRoot(currentAST, tmp311_AST);
					match(LNOT);
					break;
				}
				default:
				{
					break _loop3162;
				}
				}
			} while (true);
			}
			lookup_expr();
			astFactory.addASTChild(currentAST, returnAST);
			unary_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_30);
			} else {
			  throw ex;
			}
		}
		returnAST = unary_expr_AST;
	}
	
	public final void fp_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST fp_expr_AST = null;
		
		try {      // for error handling
			unary_expr();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3166:
			do {
				if (((LA(1) >= MUL_F && LA(1) <= LITERAL_pow))) {
					{
					switch ( LA(1)) {
					case MUL_F:
					{
						AST tmp312_AST = null;
						tmp312_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp312_AST);
						match(MUL_F);
						break;
					}
					case MUL_FD:
					{
						AST tmp313_AST = null;
						tmp313_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp313_AST);
						match(MUL_FD);
						break;
					}
					case MUL_FQ:
					{
						AST tmp314_AST = null;
						tmp314_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp314_AST);
						match(MUL_FQ);
						break;
					}
					case MUL_FSD:
					{
						AST tmp315_AST = null;
						tmp315_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp315_AST);
						match(MUL_FSD);
						break;
					}
					case MUL_FDQ:
					{
						AST tmp316_AST = null;
						tmp316_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp316_AST);
						match(MUL_FDQ);
						break;
					}
					case DIV_F:
					{
						AST tmp317_AST = null;
						tmp317_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp317_AST);
						match(DIV_F);
						break;
					}
					case DIV_FD:
					{
						AST tmp318_AST = null;
						tmp318_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp318_AST);
						match(DIV_FD);
						break;
					}
					case DIV_FQ:
					{
						AST tmp319_AST = null;
						tmp319_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp319_AST);
						match(DIV_FQ);
						break;
					}
					case PLUS_F:
					{
						AST tmp320_AST = null;
						tmp320_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp320_AST);
						match(PLUS_F);
						break;
					}
					case PLUS_FD:
					{
						AST tmp321_AST = null;
						tmp321_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp321_AST);
						match(PLUS_FD);
						break;
					}
					case PLUS_FQ:
					{
						AST tmp322_AST = null;
						tmp322_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp322_AST);
						match(PLUS_FQ);
						break;
					}
					case MINUS_F:
					{
						AST tmp323_AST = null;
						tmp323_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp323_AST);
						match(MINUS_F);
						break;
					}
					case MINUS_FD:
					{
						AST tmp324_AST = null;
						tmp324_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp324_AST);
						match(MINUS_FD);
						break;
					}
					case MINUS_FQ:
					{
						AST tmp325_AST = null;
						tmp325_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp325_AST);
						match(MINUS_FQ);
						break;
					}
					case LITERAL_pow:
					{
						AST tmp326_AST = null;
						tmp326_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp326_AST);
						match(LITERAL_pow);
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					unary_expr();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3166;
				}
				
			} while (true);
			}
			fp_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_33);
			} else {
			  throw ex;
			}
		}
		returnAST = fp_expr_AST;
	}
	
	public final void arith_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST arith_expr_AST = null;
		
		try {      // for error handling
			fp_expr();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3170:
			do {
				if ((_tokenSet_34.member(LA(1)))) {
					{
					switch ( LA(1)) {
					case MOD:
					{
						AST tmp327_AST = null;
						tmp327_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp327_AST);
						match(MOD);
						break;
					}
					case MUL:
					{
						AST tmp328_AST = null;
						tmp328_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp328_AST);
						match(MUL);
						break;
					}
					case DIV:
					{
						AST tmp329_AST = null;
						tmp329_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp329_AST);
						match(DIV);
						break;
					}
					case SMUL:
					{
						AST tmp330_AST = null;
						tmp330_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp330_AST);
						match(SMUL);
						break;
					}
					case SDIV:
					{
						AST tmp331_AST = null;
						tmp331_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp331_AST);
						match(SDIV);
						break;
					}
					case SMOD:
					{
						AST tmp332_AST = null;
						tmp332_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp332_AST);
						match(SMOD);
						break;
					}
					case PLUS:
					{
						AST tmp333_AST = null;
						tmp333_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp333_AST);
						match(PLUS);
						break;
					}
					case MINUS:
					{
						AST tmp334_AST = null;
						tmp334_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp334_AST);
						match(MINUS);
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					fp_expr();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3170;
				}
				
			} while (true);
			}
			arith_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_35);
			} else {
			  throw ex;
			}
		}
		returnAST = arith_expr_AST;
	}
	
	public final void bit_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST bit_expr_AST = null;
		
		try {      // for error handling
			arith_expr();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3174:
			do {
				if (((LA(1) >= LITERAL_rlc && LA(1) <= XORNOT))) {
					{
					switch ( LA(1)) {
					case LITERAL_rlc:
					{
						AST tmp335_AST = null;
						tmp335_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp335_AST);
						match(LITERAL_rlc);
						break;
					}
					case LITERAL_rrc:
					{
						AST tmp336_AST = null;
						tmp336_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp336_AST);
						match(LITERAL_rrc);
						break;
					}
					case LITERAL_rl:
					{
						AST tmp337_AST = null;
						tmp337_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp337_AST);
						match(LITERAL_rl);
						break;
					}
					case LITERAL_rr:
					{
						AST tmp338_AST = null;
						tmp338_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp338_AST);
						match(LITERAL_rr);
						break;
					}
					case RSHIFT:
					{
						AST tmp339_AST = null;
						tmp339_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp339_AST);
						match(RSHIFT);
						break;
					}
					case LSHIFT:
					{
						AST tmp340_AST = null;
						tmp340_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp340_AST);
						match(LSHIFT);
						break;
					}
					case RSHIFTA:
					{
						AST tmp341_AST = null;
						tmp341_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp341_AST);
						match(RSHIFTA);
						break;
					}
					case OR:
					{
						AST tmp342_AST = null;
						tmp342_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp342_AST);
						match(OR);
						break;
					}
					case ORNOT:
					{
						AST tmp343_AST = null;
						tmp343_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp343_AST);
						match(ORNOT);
						break;
					}
					case AND:
					{
						AST tmp344_AST = null;
						tmp344_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp344_AST);
						match(AND);
						break;
					}
					case ANDNOT:
					{
						AST tmp345_AST = null;
						tmp345_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp345_AST);
						match(ANDNOT);
						break;
					}
					case XOR:
					{
						AST tmp346_AST = null;
						tmp346_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp346_AST);
						match(XOR);
						break;
					}
					case XORNOT:
					{
						AST tmp347_AST = null;
						tmp347_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp347_AST);
						match(XORNOT);
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					arith_expr();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3174;
				}
				
			} while (true);
			}
			bit_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_36);
			} else {
			  throw ex;
			}
		}
		returnAST = bit_expr_AST;
	}
	
	public final void cond_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST cond_expr_AST = null;
		
		try {      // for error handling
			bit_expr();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3178:
			do {
				if (((LA(1) >= EQ && LA(1) <= GEU))) {
					{
					switch ( LA(1)) {
					case EQ:
					{
						AST tmp348_AST = null;
						tmp348_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp348_AST);
						match(EQ);
						break;
					}
					case NE:
					{
						AST tmp349_AST = null;
						tmp349_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp349_AST);
						match(NE);
						break;
					}
					case LT:
					{
						AST tmp350_AST = null;
						tmp350_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp350_AST);
						match(LT);
						break;
					}
					case GT:
					{
						AST tmp351_AST = null;
						tmp351_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp351_AST);
						match(GT);
						break;
					}
					case LE:
					{
						AST tmp352_AST = null;
						tmp352_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp352_AST);
						match(LE);
						break;
					}
					case GE:
					{
						AST tmp353_AST = null;
						tmp353_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp353_AST);
						match(GE);
						break;
					}
					case LTU:
					{
						AST tmp354_AST = null;
						tmp354_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp354_AST);
						match(LTU);
						break;
					}
					case GTU:
					{
						AST tmp355_AST = null;
						tmp355_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp355_AST);
						match(GTU);
						break;
					}
					case LEU:
					{
						AST tmp356_AST = null;
						tmp356_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp356_AST);
						match(LEU);
						break;
					}
					case GEU:
					{
						AST tmp357_AST = null;
						tmp357_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp357_AST);
						match(GEU);
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					bit_expr();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3178;
				}
				
			} while (true);
			}
			cond_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_37);
			} else {
			  throw ex;
			}
		}
		returnAST = cond_expr_AST;
	}
	
	public final void log_expr() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST log_expr_AST = null;
		
		try {      // for error handling
			cond_expr();
			astFactory.addASTChild(currentAST, returnAST);
			{
			_loop3182:
			do {
				if ((LA(1)==LAND||LA(1)==LOR)) {
					{
					switch ( LA(1)) {
					case LAND:
					{
						AST tmp358_AST = null;
						tmp358_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp358_AST);
						match(LAND);
						break;
					}
					case LOR:
					{
						AST tmp359_AST = null;
						tmp359_AST = astFactory.create(LT(1));
						astFactory.makeASTRoot(currentAST, tmp359_AST);
						match(LOR);
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					cond_expr();
					astFactory.addASTChild(currentAST, returnAST);
				}
				else {
					break _loop3182;
				}
				
			} while (true);
			}
			log_expr_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_12);
			} else {
			  throw ex;
			}
		}
		returnAST = log_expr_AST;
	}
	
	public final void fast_entry() throws RecognitionException, TokenStreamException {
		
		returnAST = null;
		ASTPair currentAST = new ASTPair();
		AST fast_entry_AST = null;
		
		try {      // for error handling
			AST tmp360_AST = null;
			tmp360_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp360_AST);
			match(NAME);
			AST tmp361_AST = null;
			tmp361_AST = astFactory.create(LT(1));
			astFactory.makeASTRoot(currentAST, tmp361_AST);
			match(INDEX);
			AST tmp362_AST = null;
			tmp362_AST = astFactory.create(LT(1));
			astFactory.addASTChild(currentAST, tmp362_AST);
			match(NAME);
			fast_entry_AST = (AST)currentAST.root;
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		returnAST = fast_entry_AST;
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"SEMI",
		"NUM",
		"NAME",
		"EQUATE",
		"PLUS",
		"MINUS",
		"\"INTEGER\"",
		"\"FLOAT\"",
		"COMMA",
		"REG_ID",
		"INDEX",
		"LSQUARE",
		"RSQUARE",
		"\"COVERS\"",
		"TO",
		"\"SHARES\"",
		"AT",
		"\"OPERAND\"",
		"LCURLY",
		"RCURLY",
		"ASSIGNTYPE",
		"\"ENDIANNESS\"",
		"\"BIG\"",
		"\"LITTLE\"",
		"LPAREN",
		"RPAREN",
		"QUOTE",
		"DECOR",
		"MOD",
		"MUL",
		"DIV",
		"SMUL",
		"SDIV",
		"SMOD",
		"\"rlc\"",
		"\"rrc\"",
		"\"rl\"",
		"\"rr\"",
		"RSHIFT",
		"LSHIFT",
		"RSHIFTA",
		"OR",
		"ORNOT",
		"AND",
		"ANDNOT",
		"XOR",
		"XORNOT",
		"MUL_F",
		"MUL_FD",
		"MUL_FQ",
		"MUL_FSD",
		"MUL_FDQ",
		"DIV_F",
		"DIV_FD",
		"DIV_FQ",
		"PLUS_F",
		"PLUS_FD",
		"PLUS_FQ",
		"MINUS_F",
		"MINUS_FD",
		"MINUS_FQ",
		"\"pow\"",
		"EQ",
		"NE",
		"LT",
		"GT",
		"LE",
		"GE",
		"LTU",
		"GTU",
		"LEU",
		"GEU",
		"PRIME",
		"DOLLAR",
		"\"halt\"",
		"UNDERSCORE",
		"\"MEMSET\"",
		"\"MEMCPY\"",
		"\"r\"",
		"\"m\"",
		"COLON",
		"FLOATNUM",
		"QUEST",
		"S_E",
		"NOT",
		"FNEG",
		"LNOT",
		"\"and\"",
		"\"or\"",
		"\"FAST\"",
		"CONSTANT",
		"TABLE",
		"CROSSP",
		"FUNCTION",
		"INSTR",
		"INSTR_NAME",
		"LOOKUP_OP",
		"RTL",
		"BUILTIN",
		"CAST",
		"REGDECL",
		"WS",
		"COMMENT",
		"DIGITS",
		"HEXDIGITS",
		"FLOAT_OR_NUM",
		"ASSIGN",
		"THEN",
		"ASSIGNTYPE_OR_MUL",
		"DOT"
	};
	
	protected void buildTokenTypeASTClassMap() {
		tokenTypeToASTClassMap=null;
	};
	
	private static final long[] mk_tokenSet_0() {
		long[] data = { 2L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 1109396544L, 536883200L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = { 1073741888L, 12288L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = { 3238035520L, 258048L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = { 16L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = { 9375760L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = { 4112L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	private static final long[] mk_tokenSet_7() {
		long[] data = { 65536L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_7 = new BitSet(mk_tokenSet_7());
	private static final long[] mk_tokenSet_8() {
		long[] data = { 562139200L, 245760L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_8 = new BitSet(mk_tokenSet_8());
	private static final long[] mk_tokenSet_9() {
		long[] data = { 289517680L, 120569856L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_9 = new BitSet(mk_tokenSet_9());
	private static final long[] mk_tokenSet_10() {
		long[] data = { 562135104L, 245760L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_10 = new BitSet(mk_tokenSet_10());
	private static final long[] mk_tokenSet_11() {
		long[] data = { -2358132750L, 1068498943L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_11 = new BitSet(mk_tokenSet_11());
	private static final long[] mk_tokenSet_12() {
		long[] data = { 1635848400L, 5488640L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_12 = new BitSet(mk_tokenSet_12());
	private static final long[] mk_tokenSet_13() {
		long[] data = { 16777280L, 245760L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_13 = new BitSet(mk_tokenSet_13());
	private static final long[] mk_tokenSet_14() {
		long[] data = { 8388624L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_14 = new BitSet(mk_tokenSet_14());
	private static final long[] mk_tokenSet_15() {
		long[] data = { 1077936208L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_15 = new BitSet(mk_tokenSet_15());
	private static final long[] mk_tokenSet_16() {
		long[] data = { 3269467218L, 536883200L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_16 = new BitSet(mk_tokenSet_16());
	private static final long[] mk_tokenSet_17() {
		long[] data = { -4294966528L, 4095L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_17 = new BitSet(mk_tokenSet_17());
	private static final long[] mk_tokenSet_18() {
		long[] data = { 268476512L, 120324096L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_18 = new BitSet(mk_tokenSet_18());
	private static final long[] mk_tokenSet_19() {
		long[] data = { 4194384L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_19 = new BitSet(mk_tokenSet_19());
	private static final long[] mk_tokenSet_20() {
		long[] data = { 8392704L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_20 = new BitSet(mk_tokenSet_20());
	private static final long[] mk_tokenSet_21() {
		long[] data = { 1073741824L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_21 = new BitSet(mk_tokenSet_21());
	private static final long[] mk_tokenSet_22() {
		long[] data = { 1073774688L, 4096L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_22 = new BitSet(mk_tokenSet_22());
	private static final long[] mk_tokenSet_23() {
		long[] data = { 3238002752L, 258048L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_23 = new BitSet(mk_tokenSet_23());
	private static final long[] mk_tokenSet_24() {
		long[] data = { 2432741488L, 120569856L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_24 = new BitSet(mk_tokenSet_24());
	private static final long[] mk_tokenSet_25() {
		long[] data = { -210714638L, 1068498943L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_25 = new BitSet(mk_tokenSet_25());
	private static final long[] mk_tokenSet_26() {
		long[] data = { 2164260928L, 245760L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_26 = new BitSet(mk_tokenSet_26());
	private static final long[] mk_tokenSet_27() {
		long[] data = { 25165904L, 245760L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_27 = new BitSet(mk_tokenSet_27());
	private static final long[] mk_tokenSet_28() {
		long[] data = { 536870912L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_28 = new BitSet(mk_tokenSet_28());
	private static final long[] mk_tokenSet_29() {
		long[] data = { -2653875248L, 416534527L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_29 = new BitSet(mk_tokenSet_29());
	private static final long[] mk_tokenSet_30() {
		long[] data = { -2659118128L, 408145919L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_30 = new BitSet(mk_tokenSet_30());
	private static final long[] mk_tokenSet_31() {
		long[] data = { -2349744142L, 1073741823L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_31 = new BitSet(mk_tokenSet_31());
	private static final long[] mk_tokenSet_32() {
		long[] data = { -933902L, 1073741823L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_32 = new BitSet(mk_tokenSet_32());
	private static final long[] mk_tokenSet_33() {
		long[] data = { 2251797154567120L, 408145916L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_33 = new BitSet(mk_tokenSet_33());
	private static final long[] mk_tokenSet_34() {
		long[] data = { 270582940416L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_34 = new BitSet(mk_tokenSet_34());
	private static final long[] mk_tokenSet_35() {
		long[] data = { 2251526571626704L, 408145916L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_35 = new BitSet(mk_tokenSet_35());
	private static final long[] mk_tokenSet_36() {
		long[] data = { 1635848400L, 408145916L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_36 = new BitSet(mk_tokenSet_36());
	private static final long[] mk_tokenSet_37() {
		long[] data = { 1635848400L, 408141824L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_37 = new BitSet(mk_tokenSet_37());
	
	}
