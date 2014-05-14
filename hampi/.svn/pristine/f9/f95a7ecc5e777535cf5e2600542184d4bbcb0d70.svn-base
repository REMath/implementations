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
package hampi.grammars;

import hampi.grammars.apps.*;

import java.util.*;

public final class Grammar extends GrammarElement{
  private final List<GrammarRule> m_rules;

  public Grammar(){
    super(GrammarElementKind.GGRAMMAR);
    m_rules = new ArrayList<GrammarRule>();
  }

  public List<GrammarRule> getRules(){
    return m_rules;
  }

  public List<GrammarProduction> getProductions(){
    List<GrammarProduction> results = new ArrayList<GrammarProduction>();
    for (GrammarRule rule : m_rules){
      results.addAll(rule.getProductions());
    }
    return results;
  }

  public List<GrammarProduction> getEpsilonProductions(){
    List<GrammarProduction> results = new ArrayList<GrammarProduction>();
    for (GrammarRule rule : m_rules){
      for (GrammarProduction prod : rule.getProductions()){
        if (prod.isEpsilonProduction()){
          results.add(prod);
        }
      }
    }
    return results;
  }

  public List<NonterminalElement> nonTerminals(){
    List<NonterminalElement> nonterminals = new ArrayList<NonterminalElement>();
    NonterminalElementCollector ntecoll = new NonterminalElementCollector(nonterminals);
    this.accept(ntecoll);
    return nonterminals;
  }

  public List<TerminalElement> terminals(){
    List<TerminalElement> terminals = new ArrayList<TerminalElement>();
    TerminalElementCollector ntecoll = new TerminalElementCollector(terminals);
    this.accept(ntecoll);
    return terminals;
  }

  public List<SpecialElement> specials(){
    List<SpecialElement> specials = new ArrayList<SpecialElement>();
    SpecialElementCollector coll = new SpecialElementCollector(specials);
    this.accept(coll);
    return specials;
  }

  // Adds rule to grammar and enforces that each nonterminal is added only once.
  public void addRule(GrammarRule rule){
    NonterminalElement nt = getNonterminal(rule.getNonterminal().getName());
    if (nt != null)
      throw new IllegalArgumentException("Grammar::AddRule rule with the same nonterminal " + rule.getNonterminal().getName() + " already exists");
    else{
      m_rules.add(rule);
    }
  }

  public void removeRule(GrammarRule ruleToRemove){
    if (ruleToRemove == null)
      throw new IllegalArgumentException("ERROR cannot remove null rule");
    boolean removed = m_rules.remove(ruleToRemove);
    if (!removed)
      throw new IllegalStateException("ERROR cannot find the rule to remove: " + ruleToRemove);
  }

  @Override
  public String toString(){
    StringBuilder out = new StringBuilder();
    SortedSet<GrammarRule> sorted = new TreeSet<GrammarRule>(GrammarElement.TOSTRING_ORDER);
    sorted.addAll(m_rules);
    for (GrammarRule rule : sorted){
      out.append(rule.toString());
      out.append("\n");
    }
    return out.toString();
  }

  @Override
  public void accept(GrammarVisitor v){
    boolean b = v.visitGrammar(this);
    if (!b)
      return;

    //make copy to avoid concurrent modifications
    for (GrammarRule rule : new ArrayList<GrammarRule>(m_rules)){
      rule.accept(v);
    }
  }

  // Returns the nonterminal for the given name, or null if none exists
  public NonterminalElement getNonterminal(String name){
    GrammarRule rule = getRule(name);
    if (rule == null)
      return null;
    return rule.getNonterminal();
  }

  public GrammarRule getRule(NonterminalElement nte){
    if (nte == null)
      throw new IllegalArgumentException("ERROR: Grammar::GetRule null argument");
    return getRule(nte.getName());
  }

  public GrammarRule getRule(String nonterminalName){
    for (GrammarRule rule : m_rules){
      if (rule.getNonterminal().getName().equals(nonterminalName))
        return rule;
    }
    return null;
  }

  public boolean isCNF(){
    for (GrammarProduction prod : getProductions()){
      List<GrammarProductionElement> els = prod.getElements();
      if (els.size() > 2)
        return false;
      if (els.size() == 1){
        if (els.get(0).getKind() != GrammarElementKind.GTERMINAL && els.get(0).getKind() != GrammarElementKind.GSPECIAL)
          return false;
      }
      if (els.size() == 2){
        if (els.get(0).getKind() != GrammarElementKind.GNONTERMINAL || els.get(1).getKind() != GrammarElementKind.GNONTERMINAL)
          return false;
      }
    }
    return true;
  }

  public Grammar makeCopy(){
    Grammar result = new Grammar();
    for (GrammarRule r : m_rules){
      result.addRule(r.makeCopy(result));
    }
    return result;
  }

  public boolean containsEpsilonProduction(String startSymbol){
    List<GrammarProduction> productions = getProductions(startSymbol);
    for (GrammarProduction prod : productions){
      if (prod.isEpsilonProduction())
        return true;
    }
    return false;
  }

  private List<GrammarProduction> getProductions(String startSymbol){
    return getRule(startSymbol).getProductions();
  }
}
