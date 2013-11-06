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

public final class NonterminalElement extends GrammarProductionElement{
  private final String m_str;

  public NonterminalElement(String str, Grammar g){
    super(g, GrammarElementKind.GNONTERMINAL);
    m_str = str;
  }

  public String getName(){
    return m_str;
  }

  @Override
  public String toString(){
    return m_str;
  }

  @Override
  public void accept(GrammarVisitor v){
    v.visitNonterminalElement(this);
  }

  @Override
  public boolean equalModuloMapping(GrammarProductionElement that, NonterminalElement nt1, NonterminalElement nt2){
    if (this == that)
      return true;
    if (this.getKind() != that.getKind())
      return false;
    NonterminalElement pThat = (NonterminalElement) that;

    if (this.getName().equals(pThat.getName()))
      return true;

    return nt1 != null && nt2 != null && nt1.getName().equals(this.getName()) && nt2.getName().equals(pThat.getName());
  }

  @Override
  public NonterminalElement makeCopy(Grammar g){
    return new NonterminalElement(m_str, g);
  }
}
