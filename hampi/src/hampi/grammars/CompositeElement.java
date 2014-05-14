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

public abstract class CompositeElement extends GrammarProductionElement{

  protected final List<GrammarProductionElement> m_subelements;

  public CompositeElement(List<GrammarProductionElement> elems, Grammar g, GrammarElementKind kind){
    super(g, kind);
    m_subelements = elems;
  }

  public List<GrammarProductionElement> getSubElements(){
    return m_subelements;
  }

  protected final String subElementsString(){
    StringBuilder out = new StringBuilder();
    out.append("(");
    for (int i = 0; i < m_subelements.size(); i++){
      if (i > 0){
        out.append(" ");
      }
      out.append(m_subelements.get(i).toString());
    }
    out.append(")");
    return out.toString();
  }

  @Override
  public final boolean equalModuloMapping(GrammarProductionElement that, NonterminalElement nt1, NonterminalElement nt2){
    if (this == that)
      return true;
    if (this.getKind() != that.getKind())
      return false;
    CompositeElement pThat = (CompositeElement) that;
    if (this.getSubElements().size() != pThat.getSubElements().size())
      return false;
    for (int i = 0; i < getSubElements().size(); i++){
      GrammarProductionElement e1 = this.getSubElements().get(i);
      GrammarProductionElement e2 = pThat.getSubElements().get(i);
      if (!e1.equalModuloMapping(e2, nt1, nt2))
        return false;
    }
    return true;
  }

  protected final List<GrammarProductionElement> copySubelements(Grammar g){
    List<GrammarProductionElement> elems = new ArrayList<GrammarProductionElement>();
    for (GrammarProductionElement subel : m_subelements){
      elems.add(subel.makeCopy(g));
    }
    return elems;
  }
}
