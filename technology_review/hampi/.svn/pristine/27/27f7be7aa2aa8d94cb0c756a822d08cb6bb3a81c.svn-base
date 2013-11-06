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
package hampi.grammars.cykparser;

import hampi.grammars.*;
import hampi.grammars.apps.*;

import java.util.*;

/**
 * CYK parser for context free languages. It works for any grammar in Chomsky
 * Normal Form. The code is implemented according to the recipe on wikipedia.
 */
public final class CYKParser{
  private final Grammar                        m_grammar;
  private final List<GrammarProductionElement> m_terminalsAndNonterminals;
  private final List<GrammarProduction>        m_productions;

  private List<ParseTree>[][][]                m_parseTable;
  private String[]                             m_tokens;
  private GrammarProductionElement             m_startSymbol;

  public CYKParser(Grammar g){
    if (!g.isCNF())
      throw new IllegalArgumentException("grammar not in Chomsky Normal Form\n:" + g);
    this.m_grammar = g;
    this.m_terminalsAndNonterminals = terminalsAndNonTerminals();
    this.m_productions = g.getProductions();
  }

  private int idx(GrammarProductionElement elem){
    return m_terminalsAndNonterminals.indexOf(elem);//XXX slow, could cache
  }

  /**
   * Parses the given token list and returns all parse trees that are rooted in
   * the given nonterminal. Returns empty list if the token list cannot be
   * parsed.
   */
  public List<ParseTree> parse(String[] tokens, String startSymbol){
    if (tokens == null || tokens.length == 0)
      throw new IllegalArgumentException("invalid string to parse " + tokens);
    m_parseTable = initialize(tokens);
    m_tokens = tokens;
    m_startSymbol = m_grammar.getNonterminal(startSymbol);
    if (m_startSymbol == null)
      throw new IllegalArgumentException("start symbol " + startSymbol + " not found");

    //   For each i = 1 to n
    //      For each unit production Rj -> ai, set P[i,1,j] = true.
    int n = tokens.length;
    List<ParseTree>[][][] P = m_parseTable;

    for (int i = 0; i < n; i++){
      String ai = tokens[i];
      if (ai.length() == 0)
        throw new IllegalArgumentException("empty token:" + Arrays.toString(tokens));

      for (GrammarProduction prod : m_productions){
        if (prod.getElements().size() == 1){
          GrammarProductionElement rhs = prod.getElements().get(0);
          String name;
          if (rhs.getKind() == GrammarElementKind.GTERMINAL){
            name = ((TerminalElement) rhs).getNameNoQuotes();
          }else if (rhs.getKind() == GrammarElementKind.GSPECIAL){
            name = ((SpecialElement) rhs).getName();
          }else
            throw new IllegalStateException("invalid element " + rhs);

          if (name.equals(ai)){
            int j = idx(prod.getNonterminal());
            P[i][1][j].add(new ParseTree(prod.getNonterminal(), rhs));
          }
        }
      }
    }
    //For each i = 2 to n -- Length of span
    // For each j = 1 to n-i+1 -- Start of span
    //   For each k = 1 to i-1 -- Partition of span
    //     For each production RA -> RB RC
    //       If P[j,k,B] and P[j+k,i-k,C] then set P[j,i,A] = true
    for (int i = 2; i <= n; i++){
      for (int j = 0; j <= n - i; j++){
        for (int k = 1; k <= i - 1; k++){
          for (GrammarProduction prod : m_productions){
            if (prod.getElements().size() == 2){
              NonterminalElement RA = prod.getNonterminal();
              NonterminalElement RB = (NonterminalElement) prod.getElements().get(0);
              NonterminalElement RC = (NonterminalElement) prod.getElements().get(1);
              int B = idx(RB);
              List<ParseTree> lefts = P[j][k][B];
              int C = idx(RC);
              List<ParseTree> rights = P[j + k][i - k][C];
              if (!lefts.isEmpty() && !rights.isEmpty()){
                int A = idx(RA);
                for (ParseTree right : rights){
                  for (ParseTree left : lefts){
                    P[j][i][A].add(new ParseTree(RA, left, right));
                  }
                }
              }
            }
          }
        }
      }
    }

    return readSolutionFromTable();
  }

  @SuppressWarnings("unchecked")
  private List<ParseTree>[][][] initialize(String[] tokens){
    int r = m_terminalsAndNonterminals.size();
    int n = tokens.length;
    List<ParseTree>[][][] P = new List[n][n + 1][r];
    for (int i = 0; i < P.length; i++){
      P[i] = new List[n + 1][r];
      for (int j = 0; j < P[i].length; j++){
        P[i][j] = new List[r];
        for (int k = 0; k < r; k++){
          P[i][j][k] = new ArrayList<ParseTree>(1);
        }
      }
    }
    return P;
  }

  private List<GrammarProductionElement> terminalsAndNonTerminals(){
    List<NonterminalElement> nonterminals = new ArrayList<NonterminalElement>();
    NonterminalElementCollector ntecoll = new NonterminalElementCollector(nonterminals);
    m_grammar.accept(ntecoll);

    List<TerminalElement> terminals = new ArrayList<TerminalElement>();
    TerminalElementCollector tcoll = new TerminalElementCollector(terminals);
    m_grammar.accept(tcoll);

    List<GrammarProductionElement> result = new ArrayList<GrammarProductionElement>();
    result.addAll(nonterminals);
    result.addAll(terminals);
    return result;
  }

  private List<ParseTree> readSolutionFromTable(){
    // any of P[1,n,x] is true (x is iterated over the set s, where s are all the indices for Rs)

    List<ParseTree>[][][] P = m_parseTable;
    return P[0][m_tokens.length][idx(m_startSymbol)];
  }
}
