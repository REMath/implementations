/*******************************************************************************
 * The MIT License
 * 
 * Copyright (c) 2008 Adam Kiezun
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ******************************************************************************/
package hampi.grammars.parser;

import hampi.grammars.*;
import hampi.grammars.apps.GramgenException;
import hampi.grammars.lexer.*;

import java.io.IOException;
import java.util.*;

/**
 * Takes an input file and returns a parse tree.
 */
public final class Parser{

  private final Lexer m_lexer;

  public Parser(String fname) throws IOException{
    m_lexer = new Lexer(fname);
  }

  // called when an unexpected token is found.
  private void unexpected(Token t, String token){
    System.out.println("Parse: unexpected token " + t.m_kind.toString() + " line " + t.m_line + " while looking for " + token + "\n");
    throw new GramgenException(m_lexer.getReadTokenCount());
  }

  // checks that the next token if of the expected kind and advances the
  // current token pointer.
  private void consumeToken(TokenKind kind){
    Token t = m_lexer.next();
    if (t.m_kind != kind){
      unexpected(t, "token of kind " + kind);
    }
  }

  // Parse the token stream and return the grammar.
  private Grammar parseGrammar(){
    Grammar g = new Grammar();

    while (m_lexer.lookahead() != TokenKind.TEOF){
      GrammarRule rule = parseRule(g);
      g.addRule(rule);
    }

    return g;
  }

  private GrammarRule parseRule(Grammar g){
    GrammarRule gr = new GrammarRule();

    // first, nonterminal
    Token t = m_lexer.next();
    if (t.m_kind != TokenKind.TNONTERMINAL){
      unexpected(t, "TNONTERMINAL");
    }
    NonterminalToken ntt = (NonterminalToken) t;
    NonterminalElement nt = new NonterminalElement(ntt.m_str, g);
    gr.setNonterminal(nt);

    // second, equals sign
    consumeToken(TokenKind.TEQUALS);

    // third, righ-hand-side elements, separated by bar, ended by semicolon
    while (m_lexer.lookahead() != TokenKind.TSEMICOLON){
      GrammarProduction rhs = parseProduction(g, gr);
      gr.addProduction(rhs);
      if (m_lexer.lookahead() == TokenKind.TBAR){
        consumeToken(TokenKind.TBAR);
        if (m_lexer.lookahead() == TokenKind.TSEMICOLON) // bar just before semicolon = epsilon transition
        {
          gr.addProduction(new GrammarProduction(gr)); // epsilon
        }
      }
    }

    if (gr.getProductions().isEmpty() && m_lexer.lookahead() == TokenKind.TSEMICOLON){
      gr.addProduction(new GrammarProduction(gr)); // epsilon
    }

    // forth, semicolon that ends the grammar rule
    consumeToken(TokenKind.TSEMICOLON);
    return gr;
  }

  private GrammarProduction parseProduction(Grammar g, GrammarRule gr){
    GrammarProduction result = new GrammarProduction(gr);

    while (m_lexer.lookahead() != TokenKind.TSEMICOLON && m_lexer.lookahead() != TokenKind.TBAR){
      GrammarProductionElement element = parseProductionElement(g);
      result.addElement(element);
    }
    return result;
  }

  private GrammarProductionElement parseProductionElement(Grammar g){
    // it must start with nonterminal, terminal, special or open parenthesis
    Token t = m_lexer.next();
    switch (t.m_kind){
    case TNONTERMINAL: {
      NonterminalToken ntt = (NonterminalToken) t;
      return new NonterminalElement(ntt.m_str, g);
    }
    case TTERMINAL: {
      TerminalToken tt = (TerminalToken) t;
      return new TerminalElement(tt.m_str, g);
    }
    case TSPECIAL: {
      SpecialToken st = (SpecialToken) t;
      return new SpecialElement(st.m_str, g);
    }
    case TOPENP: {
      return parseCompositeElement(g);
    }
    default:
      unexpected(t, "TTERMINAL, TNONTERMINAL, TSPECIAL, TOPENP");
      return null;
    }
  }

  // Parse sequence of elements, until the closing parenthesis.
  // Next symbol determines whether it's and option, star or a plus element.
  private GrammarProductionElement parseCompositeElement(Grammar g){
    List<GrammarProductionElement> elems = new ArrayList<GrammarProductionElement>();

    // read until closing parenthesis
    while (m_lexer.lookahead() != TokenKind.TCLOSEP){
      GrammarProductionElement elem = parseProductionElement(g);
      elems.add(elem);
    }
    consumeToken(TokenKind.TCLOSEP);

    // decide what this is, based on the next token
    Token t = m_lexer.next();
    switch (t.m_kind){
    case TOPTION:
      return new OptionElement(elems, g);
    case TSTAR:
      return new StarElement(elems, g);
    case TPLUS:
      return new PlusElement(elems, g);
    default: {
      unexpected(t, "TOPTION, TSTAR or TPLUS");
      return null;
    }
    }
  }

  // Parses the token stream and returns the grammar.
  public Grammar parse(){
    Grammar g = parseGrammar();
    consumeToken(TokenKind.TEOF);
    return g;
  }
}
