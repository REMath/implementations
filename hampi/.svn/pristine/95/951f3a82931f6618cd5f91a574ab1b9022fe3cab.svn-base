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
import hampi.utils.CollectionsExt;

import java.util.*;

import jpaul.Graphs.*;

/**
 * Counts the size of the longest string generatable from each nonterminal (if a
 * bound exists).
 */
public class GeneratableStringCounter{
  public boolean terms_are_single_chars;//each terminal counts as 1 character?

  public Map<GrammarElement, Integer> getBounds(final Grammar g, boolean oneCharTerminals){
    terms_are_single_chars = oneCharTerminals;
    new GrammarSimplifier().simplify(g);//in-place

    List<NonterminalElement> nonTerminals = g.nonTerminals();
    Map<GrammarElement, Integer> result = new LinkedHashMap<GrammarElement, Integer>();
    DiGraph<NonterminalElement> graph = graph(g, nonTerminals);

    Set<NonterminalElement> bounded = boundedNonterminals(nonTerminals, graph);
    for (NonterminalElement nt : bounded){
      int bound = getBound(nt, result);
      result.put(nt, bound);
    }
    return result;
  }

  /**
   * For each bounded nonterminal, the bound is the max of sums of bounds for
   * all productions.
   */
  private int getBound(NonterminalElement nt, Map<GrammarElement, Integer> cache){
    if (cache.containsKey(nt))
      return cache.get(nt);
    Grammar g = nt.getGrammar();
    List<GrammarProduction> prods = g.getRule(nt).getProductions();
    int bound = -1;
    for (GrammarProduction prod : prods){
      int prodBound = 0;
      for (GrammarElement elem : prod.getElements()){
        if (elem.getKind() == GrammarElementKind.GTERMINAL){
          if (terms_are_single_chars){
            prodBound += 1;//count each terminal as 1 character
          }else{
            TerminalElement term = (TerminalElement) elem;
            prodBound += term.getNameNoQuotes().length();
          }
        }
        if (elem.getKind() == GrammarElementKind.GSPECIAL){
          if (terms_are_single_chars){
            prodBound += 1;
          }else
            throw new UnsupportedOperationException("not implemented yet");
        }
        if (elem.getKind() == GrammarElementKind.GNONTERMINAL){
          prodBound += getBound((NonterminalElement) elem, cache);
        }
      }
      bound = Math.max(bound, prodBound);
    }
    cache.put(nt, bound);
    return bound;
  }

  /*
   * Returns the set of nonterminals for which there is a string length bound.
   */
  private Set<NonterminalElement> boundedNonterminals(List<NonterminalElement> nonTerminals, DiGraph<NonterminalElement> graph){
    Set<NonterminalElement> unbounded = unbounded(nonTerminals, graph);
    Set<NonterminalElement> bounded = CollectionsExt.diff(new LinkedHashSet<NonterminalElement>(nonTerminals), unbounded);
    return bounded;
  }

  /*
   * Returns the set of nonterminals for which there is no string length bound.
   */
  private Set<NonterminalElement> unbounded(List<NonterminalElement> nonTerminals, DiGraph<NonterminalElement> graph){
    //if a nonterminal is in a SCC with other nonterminals, then it's unbounded because you can loop forever
    TopSortedCompDiGraph<NonterminalElement> compDiGraph = graph.getComponentDiGraph();
    Set<NonterminalElement> unbounded = new LinkedHashSet<NonterminalElement>();
    for (NonterminalElement nt : nonTerminals){
      SCComponent<NonterminalElement> path = compDiGraph.getScc(nt);
      if (path.size() != 1){
        unbounded.add(nt);
      }
    }

    //self loops
    Set<NonterminalElement> diff = CollectionsExt.diff(new LinkedHashSet<NonterminalElement>(nonTerminals), unbounded);
    for (NonterminalElement nt : diff){
      if (graph.getForwardNavigator().next(nt).contains(nt)){
        unbounded.add(nt);
      }
    }

    return graph.transitivePred(unbounded);
  }

  /*
   * Graph in which each nonterminal A is connected with B if there is a production like A -> ... B ...
   */
  private DiGraph<NonterminalElement> graph(final Grammar g, final List<NonterminalElement> nonTerminals){
    DiGraph<NonterminalElement> graph = new DiGraph<NonterminalElement>(){
      @Override
      public Collection<NonterminalElement> getRoots(){
        return nonTerminals;
      }

      @Override
      public ForwardNavigator<NonterminalElement> getForwardNavigator(){
        return new ForwardNavigator<NonterminalElement>(){
          @Override
          public List<NonterminalElement> next(NonterminalElement nt){
            GrammarRule rule = g.getRule(nt);
            List<GrammarProduction> prods = rule.getProductions();
            Set<NonterminalElement> next = new LinkedHashSet<NonterminalElement>();
            for (GrammarProduction prod : prods){
              for (GrammarElement elem : prod.getElements()){
                if (elem instanceof NonterminalElement){
                  next.add((NonterminalElement) elem);
                }
              }
            }
            return new ArrayList<NonterminalElement>(next);
          }
        };
      }
    };
    return graph;
  }
}
