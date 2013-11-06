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
 * Removes unreachable nonterminals from the grammar.
 */
public class UnreachableNonterminalRemover{
  // adds to worklist names of all nonterminals that are not yet in the
  // visited list
  private void addAllUnvisited(List<String> worklist, Set<String> visited, List<NonterminalElement> nonterminals){
    for (NonterminalElement nonterminal : nonterminals){
      String ntname = nonterminal.getName();
      if (!visited.contains(ntname) && !worklist.contains(ntname)){
        worklist.add(ntname);
      }
    }
  }

  // adds to visited names of all new nonterminals
  private void addAllUnique(Set<String> visited, List<NonterminalElement> nonterminals){
    for (NonterminalElement nonterminal : nonterminals){
      visited.add(nonterminal.getName());
    }
  }

  private void getReachableNonterminals(Set<String> visited, Grammar g, String startSymbolName){
    List<String> worklist = new ArrayList<String>();

    worklist.add(startSymbolName);

    while (!worklist.isEmpty()){
      String ntname = worklist.remove(worklist.size() - 1);

      NonterminalElement nt = g.getNonterminal(ntname);
      if (nt == null)
        throw new IllegalArgumentException("Cannot find nonterminal " + ntname + " in grammar:\n" + g.toString());
      GrammarRule rule = g.getRule(nt);

      List<NonterminalElement> nonterminals = new ArrayList<NonterminalElement>();
      NonterminalElementCollector ntecoll = new NonterminalElementCollector(nonterminals);
      rule.accept(ntecoll);// Important to only traverse the rule here, not whole grammar

      addAllUnvisited(worklist, visited, nonterminals);
      addAllUnique(visited, nonterminals);
    }
  }

  public void removeUnreachableNonterminals(Grammar g, String startSymbolName){
    Set<String> visited = new LinkedHashSet<String>();
    getReachableNonterminals(visited, g, startSymbolName);

    List<NonterminalElement> all = new ArrayList<NonterminalElement>();
    NonterminalElementCollector ntecoll = new NonterminalElementCollector(all);
    g.accept(ntecoll);

    // delete all rules in diff
    for (NonterminalElement ntelem : all){
      if (!visited.contains(ntelem.getName())){
        NonterminalElement nt = g.getNonterminal(ntelem.getName());
        if (nt == null)
          throw new IllegalStateException("cannot find nonterminal " + ntelem.getName());
        GrammarRule rule = g.getRule(nt);
        g.removeRule(rule);
      }
    }
  }
}
