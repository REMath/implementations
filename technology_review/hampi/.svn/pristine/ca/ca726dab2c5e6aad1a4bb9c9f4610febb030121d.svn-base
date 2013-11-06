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

import java.util.*;

/**
 * Simplifies the grammar by expanding all option, plus and star elements.
 * Replaces those elements with references to newly introduced nonterminals. The
 * grammar grows linearly. The grammar is modified in-place.
 */
public class GrammarSimplifier{
  private int m_newSymbolCount;

  public GrammarSimplifier(){
    m_newSymbolCount = 0;
  }

  public void simplify(Grammar g){
    for (GrammarProductionElement elem : getOptionPlusStarElements(g)){
      expand(elem);
    }
  }

  private List<GrammarProductionElement> getOptionPlusStarElements(Grammar g){
    List<GrammarProductionElement> elems = new ArrayList<GrammarProductionElement>();
    OptionPlusStarCollector collector = new OptionPlusStarCollector(elems);
    g.accept(collector);
    return elems;
  }

  private String nonterminalName(){
    return "Sym" + m_newSymbolCount++;
  }

  private void expand(GrammarProductionElement elem){
    // local class for double-dispatching
    class ElementExpander extends GrammarVisitor{
      // This is the actual replacing work.
      // The element gets replaced by a reference to a new nonterminal and a rule is added for that nonterminal.
      // The 3 booleans specify what the new rule can produce.
      // - it may contain epsilon (for option and star)
      // - it may contain the list of sub elements of the replaced element (for option and plus)
      // - it may contain a way to repeat the list of subelements (for star and plus)
      private void replaceWithNewRule(List<GrammarProductionElement> subElems, GrammarProductionElement elemToReplace, boolean includeEpsilon, boolean includeElementList, boolean includeRepetition){
        Grammar g = elemToReplace.getGrammar();
        GrammarRule newRule = new GrammarRule();

        String nonterminalName = GrammarSimplifier.this.nonterminalName();

        NonterminalElement newNonterminal = new NonterminalElement(nonterminalName, g);
        newRule.setNonterminal(newNonterminal);

        if (includeEpsilon){
          GrammarProduction epsilonRHS = new GrammarProduction(newRule);
          // no elements here = epsilon
          newRule.addProduction(epsilonRHS);
        }

        if (includeElementList){
          GrammarProduction nonEpsilonRhs = new GrammarProduction(newRule);
          for (GrammarProductionElement subElem : subElems){
            nonEpsilonRhs.addElement(subElem);
          }
          newRule.addProduction(nonEpsilonRhs);
        }
        if (includeRepetition){
          GrammarProduction repetitionRhs = new GrammarProduction(newRule);
          for (GrammarProductionElement subElem : subElems){
            repetitionRhs.addElement(subElem);
          }
          repetitionRhs.addElement(newNonterminal);
          newRule.addProduction(repetitionRhs);
        }

        GrammarElementReplacer replacer = new GrammarElementReplacer(elemToReplace, newNonterminal);
        g.accept(replacer);

        g.addRule(newRule);
      }

      @Override
      public boolean visitOptionElement(OptionElement oe){
        // replace this element with a production NewSymbol -> epsilon | oe
        replaceWithNewRule(oe.getSubElements(), oe, true, true, false);
        return false;
      }

      @Override
      public boolean visitPlusElement(PlusElement pe){
        // replace this element with a production NewSymbol -> oe | oe NewSymbol
        replaceWithNewRule(pe.getSubElements(), pe, false, true, true);
        return false;
      }

      @Override
      public boolean visitStarElement(StarElement se){
        // replace this element with a production NewSymbol -> epsilon | oe NewSymbol
        replaceWithNewRule(se.getSubElements(), se, true, false, true);
        return false;
      }
    }

    ElementExpander expander = new ElementExpander();
    elem.accept(expander);
  }
}
