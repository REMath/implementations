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

import java.util.List;

/**
 * Collects all terminals from the grammar.
 */
public class TerminalElementCollector extends GrammarVisitor{
  private final List<TerminalElement> m_acc; // accumulated result

  public TerminalElementCollector(List<TerminalElement> acc){
    m_acc = acc;
  }

  // Adds argument to the List, unless another element with same name is already there.
  @Override
  public boolean visitTerminalElement(TerminalElement te){
    for (TerminalElement elem : m_acc){
      if (elem.getName().equals(te.getName()))
        return true;
    }
    m_acc.add(te);
    return true;
  }
}
