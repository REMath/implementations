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

public final class TerminalElement extends GrammarProductionElement{
  private final String m_str;

  public TerminalElement(String str, Grammar g){
    super(g, GrammarElementKind.GTERMINAL);
    m_str = str;
    assert m_str.length() >= 3 : str;
  }

  public String getName(){
    return m_str;
  }

  public String getNameNoQuotes(){
    return getName().substring(1, getName().length() - 1);
  }

  @Override
  public String toString(){
    return m_str;
  }

  @Override
  public void accept(GrammarVisitor v){
    v.visitTerminalElement(this);
  }

  // For terminals, mapping nonterminal name will not change anything
  @Override
  public boolean equalModuloMapping(GrammarProductionElement that, NonterminalElement nt1, NonterminalElement nt2){
    if (this == that)
      return true;
    if (this.getKind() != that.getKind())
      return false;
    TerminalElement pThat = (TerminalElement) that;
    return this.getName().equals(pThat.getName());
  }

  @Override
  public TerminalElement makeCopy(Grammar g){
    return new TerminalElement(m_str, g);
  }
}
