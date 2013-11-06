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

import java.util.*;

public final class GrammarProduction extends GrammarElement{

  private GrammarRule                          m_rule;
  private final List<GrammarProductionElement> m_elements;

  public GrammarProduction(GrammarRule r){
    super(GrammarElementKind.GRULERHS);
    m_rule = r;
    m_elements = new ArrayList<GrammarProductionElement>();
  }

  public void setRule(GrammarRule rule){
    m_rule = rule;
  }

  public GrammarRule getRule(){
    return m_rule;
  }

  public void addAllElements(List<? extends GrammarProductionElement> elements){
    m_elements.addAll(elements);
  }

  public void addElement(GrammarProductionElement element){
    m_elements.add(element);
  }

  public List<GrammarProductionElement> getElements(){
    return m_elements;
  }

  @Override
  public String toString(){
    StringBuilder out = new StringBuilder();
    out.append(getNonterminal().getName());
    out.append(" = ");
    for (int i = 0; i < m_elements.size(); i++){
      GrammarProductionElement rule = m_elements.get(i);
      out.append(rule.toString());
      out.append(" ");
    }
    return out.toString();
  }

  public Object toStringNoNonterminal(){
    StringBuilder out = new StringBuilder();
    for (int i = 0; i < m_elements.size(); i++){
      GrammarProductionElement rule = m_elements.get(i);
      out.append(rule.toString());
      out.append(" ");
    }
    return out.toString();
  }

  @Override
  public void accept(GrammarVisitor v){
    boolean b = v.visitGrammarRuleRHS(this);
    if (!b)
      return;

    for (GrammarProductionElement rule : m_elements){
      rule.accept(v);
    }
  }

  // checks equality modulo simple renaming (in 'that') of nt1 to nt2
  // nt1 and nt2 may be null, and are ignored then
  public boolean equalModuloMapping(GrammarProduction that, NonterminalElement nt1, NonterminalElement nt2){
    if (this == that)
      return true;
    if (this.m_elements.size() != that.m_elements.size())
      return false;

    for (int i = 0; i < m_elements.size(); i++){
      GrammarProductionElement e1 = this.m_elements.get(i);
      GrammarProductionElement e2 = that.m_elements.get(i);
      if (!e1.equalModuloMapping(e2, nt1, nt2))
        return false;
    }
    return true;
  }

  public NonterminalElement getNonterminal(){
    return getRule().getNonterminal();
  }

  public GrammarProduction makeCopy(GrammarRule rule, Grammar g){
    GrammarProduction result = new GrammarProduction(rule);
    for (GrammarProductionElement el : m_elements){
      result.addElement(el.makeCopy(g));
    }
    return result;
  }

  public boolean isEpsilonProduction(){
    return m_elements.isEmpty();
  }
}
