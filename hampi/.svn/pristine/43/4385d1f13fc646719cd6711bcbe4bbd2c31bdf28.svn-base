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

import java.util.List;

//Repetition of a sequence of elements - repeats any number of times, maybe 0.
public final class StarElement extends CompositeElement{

  public StarElement(List<GrammarProductionElement> elems, Grammar g){
    super(elems, g, GrammarElementKind.GSTAR);
  }

  @Override
  public String toString(){
    return subElementsString() + "*";
  }

  @Override
  public void accept(GrammarVisitor v){
    boolean b = v.visitStarElement(this);
    if (!b)
      return;

    for (GrammarProductionElement elem : m_subelements){
      elem.accept(v);
    }
  }

  @Override
  public StarElement makeCopy(Grammar g){
    List<GrammarProductionElement> elems = copySubelements(g);
    return new StarElement(elems, g);
  }
}
