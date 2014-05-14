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
package hampi.grammars.cykparser;

import hampi.grammars.*;
import hampi.utils.Utils;

/**
 * Parse tree created by the CYK parser.
 */
public final class ParseTree{
  private final NonterminalElement m_elem;
  private GrammarProductionElement m_term;
  private final ParseTree          m_right;
  private final ParseTree          m_left;

  /**
   * Creates leaf node.
   */
  public ParseTree(NonterminalElement elem, GrammarProductionElement rhs){
    this(elem, null, null);
    this.m_term = rhs;
  }

  /**
   * Creates internal node.
   */
  public ParseTree(NonterminalElement elem, ParseTree t1, ParseTree t2){
    this.m_elem = elem;
    this.m_left = t1;
    this.m_right = t2;
    if (m_elem == null && t1 == null && t2 != null)
      throw new IllegalArgumentException("null subtree");
  }

  @Override
  public String toString(){
    return toStringWitIndent(0);
  }

  public String toStringWitIndent(int indent){
    if (m_left == null || m_right == null)
      return Utils.spaces(indent) + m_elem.toString() + "(" + m_term.toString() + ")";
    else
      return Utils.spaces(indent) + m_elem.toString() + "(\n" + m_left.toStringWitIndent(indent + 2) + "\n" + m_right.toStringWitIndent(indent + 2) + ")";
  }
}
