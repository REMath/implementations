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
package hampi.grammars.apps;

import hampi.grammars.*;

import java.util.*;

/**
 * Converts the grammar to Chomsky Normal Form. This is done using the algorithm
 * given by Richard Cole "Converting CFGs to CNF".
 */
public final class CNFConverter{

  public Grammar convertToCNF(Grammar g, String startSymbol){
    return convertToCNF(g, startSymbol, new ArrayList<Grammar>(4));
  }

  /**
   * this is only for testing - adds intermediate grammars to the list
   */
  public Grammar convertToCNF(Grammar g, String startSymbol, List<Grammar> intermediateGrammars){
    if (g == null)
      throw new IllegalArgumentException("null argument");
    if (g.isCNF())
      return g;
    NonterminalElement start = g.getNonterminal(startSymbol);
    if (start == null)
      throw new IllegalArgumentException("cannot find start symbol:\n" + g);

    Grammar result;

    result = simplifyGrammar(g);
    System.out.println(result);

    intermediateGrammars.add(result.makeCopy());

    result = createNonterminalForEachTerminal(result);
    intermediateGrammars.add(result.makeCopy());

    result = makeAllProductionsShort(result);
    intermediateGrammars.add(result.makeCopy());

    result = introduceNewStartingSymbol(result, start);
    intermediateGrammars.add(result.makeCopy());

    result = eliminateEpsilonProductions(result, startSymbol);
    intermediateGrammars.add(result.makeCopy());

    result = eliminateUnitProductions(result);
    return result;
  }

  private Grammar simplifyGrammar(Grammar g){
    GrammarSimplifier simplifier = new GrammarSimplifier();
    Grammar copy = g.makeCopy();
    simplifier.simplify(copy);
    return copy;
  }

  /**
   * For each terminal a (and special), we introduce a new variable, Ua say, add
   * a rule Ua -> a, and for each occurrence of a in a string of length 2 or
   * more on the right hand side of a rule, replace a by Ua. Clearly, the
   * generated language is unchanged. Example: If we have the rule A -> B a,
   * this is replaced by Ua -> a, A -> B Ua.
   */
  private Grammar createNonterminalForEachTerminal(Grammar result){
    //collect all terminals
    Set<GrammarProductionElement> termAndSpecials = getAllTermAndSpecials(result);

    //create a nonterminal for each terminal
    Map<GrammarProductionElement, NonterminalElement> newNonerminals = new LinkedHashMap<GrammarProductionElement, NonterminalElement>();
    for (GrammarProductionElement termOrSpecial : termAndSpecials){
      String name;
      if (termOrSpecial.getKind() == GrammarElementKind.GTERMINAL){
        name = ((TerminalElement) termOrSpecial).getNameNoQuotes();
      }else if (termOrSpecial.getKind() == GrammarElementKind.GSPECIAL){
        name = ((SpecialElement) termOrSpecial).getNameNoDelimiters();
      }else
        throw new IllegalStateException("incorrect kind: " + termOrSpecial);

      newNonerminals.put(termOrSpecial, new NonterminalElement("U_" + name, result));
    }

    //replace references to terminals with references to nonterminals, in rules with 2 or more string on RHS
    Set<GrammarProductionElement> replacedTerminals = new LinkedHashSet<GrammarProductionElement>();
    for (GrammarProduction production : result.getProductions()){
      if (production.getElements().size() >= 2){//only do this for productions of 2 or more strings
        for (GrammarProductionElement termOrSpecial : production.getElements()){
          if (termAndSpecials.contains(termOrSpecial)){
            production.accept(new GrammarElementReplacer(termOrSpecial, newNonerminals.get(termOrSpecial)));
            replacedTerminals.add(termOrSpecial);
          }
        }
      }
    }

    //add unit productions for the replaced terminals
    for (GrammarProductionElement termOrSpecial : replacedTerminals){
      NonterminalElement nonterminal = newNonerminals.get(termOrSpecial);
      GrammarRule newRule = new GrammarRule();
      GrammarProduction rhs = new GrammarProduction(newRule);
      rhs.addElement(termOrSpecial);
      newRule.setNonterminal(nonterminal);
      newRule.addProduction(rhs);
      result.addRule(newRule);
    }

    return result.makeCopy();
  }

  private static Set<GrammarProductionElement> getAllTermAndSpecials(Grammar grammar){
    List<TerminalElement> terminals = new ArrayList<TerminalElement>();
    TerminalElementCollector tec = new TerminalElementCollector(terminals);
    grammar.accept(tec);

    List<SpecialElement> nonTerminals = new ArrayList<SpecialElement>();
    SpecialElementCollector ntec = new SpecialElementCollector(nonTerminals);
    grammar.accept(ntec);

    Set<GrammarProductionElement> result = new LinkedHashSet<GrammarProductionElement>();
    result.addAll(terminals);
    result.addAll(nonTerminals);
    return result;
  }

  /**
   * For each production with 3 or more variables on the right-hand side, we
   * replace it with a new collection of production each with 2 nonterminals on
   * RHS. Suppose there is a production U = W1 W2...Wk, for some k >= 3. Then we
   * create new variables X2,X3,...,Xk-1, and replace the prior production with
   * the productions: U = W1 X2; X2 = W2 X3;...; ... Xk-2 = Wk-2 Xk-1; Xk-1 =
   * Wk-1 Wk;
   */
  private Grammar makeAllProductionsShort(Grammar result){
    int i = 0;
    for (GrammarProduction production : result.getProductions()){
      int rhsSize = production.getElements().size();
      GrammarRule rule = production.getRule();
      if (rhsSize > 2){
        rule.getProductions().remove(production);
        int toCreate = rhsSize - 2;
        NonterminalElement[] newNonterminals = new NonterminalElement[toCreate];

        for (int j = 0; j < newNonterminals.length; j++){
          newNonterminals[j] = new NonterminalElement("X" + i++, result);
        }

        for (int j = 0; j < newNonterminals.length + 1; j++){

          GrammarRule ruleToAddNewProdTo;
          if (j == 0){
            ruleToAddNewProdTo = rule;
          }else{
            ruleToAddNewProdTo = new GrammarRule();
            ruleToAddNewProdTo.setNonterminal(newNonterminals[j - 1]);
          }

          GrammarProduction newProd = new GrammarProduction(ruleToAddNewProdTo);
          newProd.addElement(production.getElements().get(j));

          if (j == newNonterminals.length){
            newProd.addElement(production.getElements().get(j + 1));
          }else{
            newProd.addElement(newNonterminals[j]);
          }

          ruleToAddNewProdTo.getProductions().add(newProd);
          if (j != 0){
            result.addRule(ruleToAddNewProdTo);
          }
        }
      }
    }
    return result;
  }

  /**
   * Replace each occurrence of the start symbol S with the variable S_prime and
   * add the production S -> S_prime
   */
  private Grammar introduceNewStartingSymbol(Grammar result, NonterminalElement start){
    NonterminalElement nt = new NonterminalElement(start.getName() + "_prime", result);
    GrammarElementReplacer ger = new GrammarElementReplacer(start, nt);
    result.accept(ger);
    GrammarRule newRule = new GrammarRule();
    newRule.setNonterminal(start);
    GrammarProduction newRHS = new GrammarProduction(newRule);
    newRHS.addElement(nt);
    newRule.addProduction(newRHS);
    result.addRule(newRule);
    return result;
  }

  /** Eliminate epsilon productions */
  private Grammar eliminateEpsilonProductions(Grammar result, String startSymbol){
    EpsilonProductionRemover epr = new EpsilonProductionRemover();
    epr.removeEpsilonProductions(result, startSymbol);
    return result;
  }

  /** eliminate unit productions N->T */
  private Grammar eliminateUnitProductions(Grammar result){
    return new UnitProductionRemover().removeUnitProductions(result);
  }
}
