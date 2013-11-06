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
 * Removes epsilon productions from the grammar. XXX this code is potentially
 * bogus. Use a textbook algorithm.
 */
public final class EpsilonProductionRemover{
  public void removeEpsilonProductions(Grammar g, String startSymbol){
    GrammarSimplifier simplifier = new GrammarSimplifier();
    simplifier.simplify(g);

    NonterminalElement startNonterminal = g.getNonterminal(startSymbol);
    Set<GrammarProduction> epsilonProductions = getEpsilonProductions(g, startNonterminal);
    while (!epsilonProductions.isEmpty()){
      removeXtoXproductions(g);
      for (GrammarProduction epsilonProd : epsilonProductions){
        if (!epsilonProd.getNonterminal().equals(startNonterminal)){
          removeEpsilonProduction(epsilonProd, g);
        }
      }
      epsilonProductions = getEpsilonProductions(g, startNonterminal);
    }

    UnreachableNonterminalRemover nonterminalRemover = new UnreachableNonterminalRemover();
    nonterminalRemover.removeUnreachableNonterminals(g, startSymbol);
  }

  /* removes X->X productions */
  private void removeXtoXproductions(final Grammar grammar){
    for (GrammarProduction prod : grammar.getProductions()){
      if (prod.getElements().size() == 1 && prod.getNonterminal().equals(prod.getElements().get(0))){
        prod.getRule().getProductions().remove(prod);
      }
    }
  }

  public static Set<GrammarProduction> getEpsilonProductions(Grammar g, NonterminalElement startElem){
    Set<GrammarProduction> result = new LinkedHashSet<GrammarProduction>();
    for (GrammarProduction p : g.getEpsilonProductions()){
      if (p.getElements().isEmpty() && !p.getNonterminal().equals(startElem)){
        result.add(p);
      }
    }
    return result;
  }

  //N -> | X ;
  //Foo -> X A;
  private void removeEpsilonProduction(GrammarProduction epsilonProd, Grammar g){
    epsilonProd.getRule().getProductions().remove(epsilonProd);//remove the production

    NonterminalElement nonterminalToRemove = epsilonProd.getNonterminal();
    boolean empty = epsilonProd.getRule().getProductions().isEmpty();
    removeNonterminal(nonterminalToRemove, g, empty);
  }

  private void removeNonterminal(NonterminalElement nonterminalToRemove, Grammar g, boolean empty){
    Set<GrammarProduction> newProductions = new LinkedHashSet<GrammarProduction>();
    Set<GrammarProduction> toDelete = new LinkedHashSet<GrammarProduction>();
    List<GrammarProduction> prods = new ArrayList<GrammarProduction>(g.getProductions());
    while (!prods.isEmpty()){
      GrammarProduction production = prods.remove(0);
      for (int i = 0, n = production.getElements().size(); i < n; i++){
        GrammarProductionElement elem = production.getElements().get(i);
        if (elem.equals(nonterminalToRemove)){
          if (empty){
            toDelete.add(production);
          }
          //add a copy of the production, with the element removed
          GrammarProduction newProduction = new GrammarProduction(production.getRule());
          for (int j = 0, m = production.getElements().size(); j < m; j++){
            if (i != j){
              newProduction.addElement(production.getElements().get(j));
            }
          }
          newProductions.add(newProduction);
          prods.add(newProduction);
        }
      }
    }
    for (GrammarProduction newProd : newProductions){
      g.getRule(newProd.getNonterminal()).addProduction(newProd);
    }
    for (GrammarProduction grammarProduction : toDelete){
      grammarProduction.getRule().getProductions().remove(grammarProduction);
    }
  }
}
