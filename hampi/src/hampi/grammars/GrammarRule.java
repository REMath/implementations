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

//Rule in the grammar - lhs is a nonterminal, rhs is a set of rhs elements.
public final class GrammarRule extends GrammarElement{
  private final List<GrammarProduction> m_rhss;
  private NonterminalElement            m_nonterminal;

  public GrammarRule(){
    super(GrammarElementKind.GRULE);
    m_rhss = new ArrayList<GrammarProduction>();
  }

  public void setNonterminal(NonterminalElement nonterminal){
    m_nonterminal = nonterminal;
  }

  public NonterminalElement getNonterminal(){
    return m_nonterminal;
  }

  public List<GrammarProduction> getProductions(){
    return m_rhss;
  }

  public void addProduction(GrammarProduction rhs){
    m_rhss.add(rhs);
  }

  public void removeProduction(GrammarProduction rhs){
    m_rhss.remove(rhs);
  }

  @Override
  public String toString(){
    StringBuilder out = new StringBuilder();
    out.append(m_nonterminal.toString());
    out.append(" = ");
    //sort the productions alphabetically
    SortedSet<GrammarProduction> sorted = new TreeSet<GrammarProduction>(GrammarElement.TOSTRING_ORDER);
    sorted.addAll(m_rhss);
    int i = 0;
    for (GrammarProduction production : sorted){
      if (i > 0){
        out.append(" | ");
      }
      i++;
      out.append(production.toStringNoNonterminal());//don't print nonterminal here
    }
    out.append(" ;");
    return out.toString();
  }

  @Override
  public void accept(GrammarVisitor v){
    boolean b = v.visitGrammarRule(this);
    if (!b)
      return;

    m_nonterminal.accept(v);

    for (GrammarProduction rule : m_rhss){
      rule.accept(v);
    }
  }

  // Compares the rules, but ignores the lhs nonterminal.
  // assumes that rule duplication removal was done before
  // so it's ok to say no if there are different numbers of productions for each nonterminal.
  public boolean equalsIgnoringNonterminal(GrammarRule that){
    if (this == that)
      return true;
    // ignore nonterminal, compare rhs
    if (this.getProductions().size() != that.getProductions().size())
      return false;
    // every rhs in this should have a corresponsing one in that
    // (we checked sizes and assume dup removal, so checking only one way is enough)
    for (int i1 = 0; i1 < this.getProductions().size(); i1++){
      GrammarProduction rhs1 = this.getProductions().get(i1);
      boolean found = false;
      for (int i2 = 0; i2 < that.getProductions().size(); i2++){
        GrammarProduction rhs2 = that.getProductions().get(i2);

        // We check equality modulo a simple re-mapping of nonterminal names.
        // S1 . "x" | S1;
        // S2 . "x" | S2;
        // Nonterminals S1 and S2 should end up begin considered equal.
        boolean equalWithMaping = rhs1.equalModuloMapping(rhs2, this.getNonterminal(), that.getNonterminal());
        if (equalWithMaping){
          found = true;
          break;
        }
      }
      if (!found)
        return false;
    }
    return true;
  }

  public GrammarRule makeCopy(Grammar g){
    GrammarRule result = new GrammarRule();
    result.setNonterminal(m_nonterminal.makeCopy(g));
    for (GrammarProduction rhs : m_rhss){
      result.addProduction(rhs.makeCopy(result, g));
    }
    return result;
  }
}
