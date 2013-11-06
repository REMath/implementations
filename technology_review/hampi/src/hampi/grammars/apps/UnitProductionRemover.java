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

import jpaul.Graphs.*;

/**
 * Removes unit rules: N -> M. This is done using the algorithm given by Richard
 * Cole "Converting CFGs to CNF".
 */
public class UnitProductionRemover{
  public Grammar removeUnitProductions(final Grammar grammar){
    DiGraph<NonterminalElement> digraph = unitProductionDependencyGraph(grammar);
    TopSortedCompDiGraph<NonterminalElement> topSort1 = digraph.getComponentDiGraph();
    for (SCComponent<NonterminalElement> scc : topSort1.vertices()){
      SortedSet<NonterminalElement> sortedElems = new TreeSet<NonterminalElement>(GrammarElement.TOSTRING_ORDER);
      sortedElems.addAll(scc.vertices());
      NonterminalElement first = sortedElems.last();
      for (NonterminalElement elemToReplace : sortedElems){
        if (elemToReplace != first){
          GrammarElementReplacer ger = new GrammarElementReplacer(elemToReplace, first);
          grammar.accept(ger);
        }
      }
    }

    //Eliminate rules X->X
    removeXtoXproductions(grammar);

    TopSortedCompDiGraph<NonterminalElement> topSort2 = digraph.getComponentDiGraph();
    for (SCComponent<NonterminalElement> scc : topSort2.incrOrder()){
      if (scc.size() > 1)
        throw new IllegalStateException("each scc should have 1 element");
      NonterminalElement nt1 = scc.vertices().iterator().next();
      for (SCComponent<NonterminalElement> prev : topSort2.getBiDiNavigator().prev(scc)){
        if (prev.size() > 1)
          throw new IllegalStateException("each scc should have 1 element");
        NonterminalElement nt2 = prev.vertices().iterator().next();

        GrammarRule nt2Rule = grammar.getRule(nt2);
        for (GrammarProduction prod : grammar.getRule(nt1).getProductions()){
          GrammarProduction copyProd = new GrammarProduction(nt2Rule);
          copyProd.addAllElements(prod.getElements());
          nt2Rule.addProduction(copyProd);
        }
        for (Iterator<GrammarProduction> iterator = nt2Rule.getProductions().iterator(); iterator.hasNext();){
          GrammarProduction p = iterator.next();

          if (p.getElements().size() == 1 && p.getElements().get(0).equals(nt1)){
            iterator.remove();
          }
        }
      }
    }
    return grammar;
  }

  private void removeXtoXproductions(final Grammar grammar){
    for (GrammarProduction prod : grammar.getProductions()){
      if (prod.getElements().size() == 1 && prod.getNonterminal().equals(prod.getElements().get(0))){
        prod.getRule().getProductions().remove(prod);
      }
    }
  }

  /*
   * Creates graph of dependencies between nonterminals in unit productions.
   */
  private DiGraph<NonterminalElement> unitProductionDependencyGraph(final Grammar result){
    DiGraph<NonterminalElement> digraph = new DiGraph<NonterminalElement>(){
      @Override
      public Collection<NonterminalElement> getRoots(){
        Set<NonterminalElement> r = new LinkedHashSet<NonterminalElement>();
        for (GrammarProduction prod : result.getProductions()){
          if (prod.getElements().size() == 1 && prod.getElements().get(0).getKind() == GrammarElementKind.GNONTERMINAL){
            r.add(prod.getNonterminal());
          }
        }
        return r;
      }

      @Override
      public ForwardNavigator<NonterminalElement> getForwardNavigator(){
        return new ForwardNavigator<NonterminalElement>(){
          public List<NonterminalElement> next(NonterminalElement vertex){
            List<NonterminalElement> r = new ArrayList<NonterminalElement>(1);
            GrammarRule rule = result.getRule(vertex);
            for (GrammarProduction prod : rule.getProductions()){
              if (prod.getElements().size() == 1 && prod.getElements().get(0).getKind() == GrammarElementKind.GNONTERMINAL){
                r.add((NonterminalElement) prod.getElements().get(0));
              }
            }
            return r;
          }
        };
      }
    };
    return digraph;
  }
}
