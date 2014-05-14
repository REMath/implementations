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

/**
 * Visitor for grammar elements. This is the default implementation that does
 * nothing. The return values indicate whether visiting should continue to
 * children of the visited node. Subclasses override only those methods that are
 * useful for them.
 */
public abstract class GrammarVisitor{
  public boolean visitGrammar(Grammar g){
    return true;
  }

  public boolean visitGrammarRule(GrammarRule gr){
    return true;
  }

  public boolean visitGrammarRuleRHS(GrammarProduction rhs){
    return true;
  }

  public boolean visitTerminalElement(TerminalElement te){
    return true;
  }

  public boolean visitNonterminalElement(NonterminalElement nte){
    return true;
  }

  public boolean visitSpecialElement(SpecialElement se){
    return true;
  }

  public boolean visitPlusElement(PlusElement pe){
    return true;
  }

  public boolean visitStarElement(StarElement se){
    return true;
  }

  public boolean visitOptionElement(OptionElement oe){
    return true;
  }
}
