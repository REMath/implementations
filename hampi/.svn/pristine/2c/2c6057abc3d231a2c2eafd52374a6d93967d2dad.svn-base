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
import hampi.utils.Pair;

import java.util.List;

/**
 * Removes duplicate productions and nonterminals.
 */
class DuplicateRemover{
  private void findDuplicateRules(boolean[] dup, List<GrammarProduction> rhss){
    for (int i1 = 0; i1 < rhss.size(); i1++){
      if (!dup[i1]){
        GrammarProduction r1 = rhss.get(i1);
        // only iterate over different productions
        for (int i2 = i1 + 1; i2 < rhss.size(); i2++){
          dup[i2] = dup[i2] || r1.equals(rhss.get(i2));
        }
      }
    }
  }

  /* returns true iff the grammar changed as the result of this call */
  private boolean removeDuplicateRules(boolean[] dup, List<GrammarProduction> rhss){
    boolean grammarChanged = false;

    // remove all dups, in reverse order to not lose indices
    for (int i = rhss.size() - 1; i >= 0; i--){
      if (dup[i]){
        grammarChanged = true;
        rhss.remove(i);
      }
    }
    return grammarChanged;
  }

  /* returns true iff the grammar changed as the result of this call */
  private boolean removeDuplicateRules(Grammar g){
    boolean grammarChanged = false;
    for (GrammarRule rule : g.getRules()){
      List<GrammarProduction> rhss = rule.getProductions();

      // lists all duplicates, initialized to all false
      boolean[] dup = new boolean[rhss.size()];
      findDuplicateRules(dup, rhss);
      grammarChanged = removeDuplicateRules(dup, rhss) || grammarChanged;

    }
    return grammarChanged;
  }

  // -----------

  /**
   * A nonterminal N1 is a duplicate of N2 if all productions for N1 are the
   * same as productions for N2, modulo renaming N1 to N2.
   * 
   * Returns a new pair of nonterminals such that one is a duplicate of the
   * other. Order is unspecified, but they will always be different
   * nonterminals. Returns NULL if no pair of duplicates exists.
   */
  private Pair<NonterminalElement, NonterminalElement> findDuplicateNonterminal(Grammar g){
    List<GrammarRule> rules = g.getRules();
    for (int i1 = 0; i1 < rules.size(); i1++){
      GrammarRule r1 = rules.get(i1);
      NonterminalElement nt1 = r1.getNonterminal();

      // only iterate over different rules
      for (int i2 = i1 + 1; i2 < rules.size(); i2++){
        GrammarRule r2 = rules.get(i2);
        NonterminalElement nt2 = r2.getNonterminal();

        if (r1.equalsIgnoringNonterminal(r2))
          return new Pair<NonterminalElement, NonterminalElement>(nt1, nt2);
      }
    }
    return null;
  }

  /* Replaces references to one nonterminal with references to another nonterminal */
  private void removeDuplicateNonterminal(Pair<NonterminalElement, NonterminalElement> dup, Grammar g){
    NonterminalElement nt1 = dup.first;
    NonterminalElement nt2 = dup.second;

    if (nt1 == nt2 || nt1.getName().equals(nt2.getName())){
      System.out.println("ERROR: RemoveDuplicateNonterminal nonterminal is not a dup of itself:" + nt1.getName() + "\n");
      throw new GramgenException(1);
    }

    // decide which to keep, which to remove. Do this in a predictable way, by sorting by name.
    NonterminalElement toKeep;
    NonterminalElement toRemove;
    if (nt1.getName().compareTo(nt2.getName()) < 0){
      toKeep = nt1;
      toRemove = nt2;
    }else{
      toKeep = nt2;
      toRemove = nt1;
    }
    GrammarElementReplacer replacer = new GrammarElementReplacer(toRemove, toKeep);
    g.accept(replacer);
  }

  /* returns true iff grammar changed as the result of this call. */
  private boolean removeDuplicateNonterminals(Grammar g){
    boolean grammarChanged = false;
    Pair<NonterminalElement, NonterminalElement> dup = findDuplicateNonterminal(g);

    // find and remove duplicates until no more exists.
    // Every removal possibly introduces new possibilities, so do fixpoint here.
    while (dup != null){
      grammarChanged = true;
      removeDuplicateNonterminal(dup, g);
      dup = findDuplicateNonterminal(g);
    }
    return grammarChanged;
  }

  /**
   * Duplication removal works by fix-point iteration and removal of one
   * duplicate at a time.
   */
  public void removeDuplicates(Grammar g){
    boolean fixpoint = false;
    do{
      boolean dupRules = removeDuplicateRules(g);
      boolean dupNonterms = removeDuplicateNonterminals(g);
      fixpoint = !dupRules && !dupNonterms;
    }while (!fixpoint);
  }
}
