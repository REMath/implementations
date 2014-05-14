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

import java.util.Comparator;

public abstract class GrammarElement{
  private final GrammarElementKind m_kind;

  public GrammarElement(GrammarElementKind m_kind){
    this.m_kind = m_kind;
  }

  public abstract void accept(GrammarVisitor v);

  public GrammarElementKind getKind(){
    return m_kind;
  }

  @Override
  public final boolean equals(Object obj){
    return obj != null && this.toString().equals(obj.toString());//this is OK here because grammars are uniquely identified by their string representation
  }

  @Override
  public final int hashCode(){
    return toString().hashCode(); //this is OK here because grammars are uniquely identified by their string representation
  }

  public static final Comparator<GrammarElement> TOSTRING_ORDER = new Comparator<GrammarElement>(){
                                                                  public int compare(GrammarElement o1, GrammarElement o2){
                                                                    return o1.toString().compareTo(o2.toString());
                                                                  }
                                                                };

  @Override
  public abstract String toString();
}
