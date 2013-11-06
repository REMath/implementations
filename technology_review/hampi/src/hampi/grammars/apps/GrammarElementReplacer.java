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
 * This is used to replace one grammar element with another, i.e., changing one
 * pointer into another Right now, only implemented for replacing RHSelements
 * For comparison, uses equals.
 */
public class GrammarElementReplacer extends GrammarVisitor{
  private final GrammarProductionElement m_oldElem;
  private final GrammarProductionElement m_newElem;

  // find the element in the list and replace it with the new one
  private void searchAndReplace(List<GrammarProductionElement> elems){
    for (int i = 0; i < elems.size(); i++){
      if (elems.get(i).equals(m_oldElem)){
        elems.set(i, m_newElem);
      }
    }
  }

  public GrammarElementReplacer(GrammarProductionElement oldElem, GrammarProductionElement newElem){
    m_oldElem = oldElem;
    m_newElem = newElem;
  }

  @Override
  public boolean visitGrammarRule(GrammarRule rule){
    if (rule.getNonterminal().equals(m_oldElem)){
      if (m_newElem.getKind() != GrammarElementKind.GNONTERMINAL){
        System.out.println("ERROR invalid kind of element " + m_newElem.getKind() + " expected GNONTERMINAL = " + GrammarElementKind.GNONTERMINAL + "\n");
        throw new GramgenException(1);
      }
      Grammar grammar = rule.getNonterminal().getGrammar();
      GrammarRule ruleToAppendTo = grammar.getRule((NonterminalElement) m_newElem);
      if (ruleToAppendTo != null){
        for (GrammarProduction prod : rule.getProductions()){
          prod.setRule(ruleToAppendTo);
          ruleToAppendTo.addProduction(prod);
          prod.accept(this);
        }
        grammar.removeRule(rule);
      }else{
        rule.setNonterminal((NonterminalElement) m_newElem);
      }
    }
    return true;
  }

  @Override
  public boolean visitGrammarRuleRHS(GrammarProduction rhs){
    searchAndReplace(rhs.getElements());
    return true;
  }

  @Override
  public boolean visitPlusElement(PlusElement pe){
    searchAndReplace(pe.getSubElements());
    return true;
  }

  @Override
  public boolean visitStarElement(StarElement se){
    searchAndReplace(se.getSubElements());
    return true;
  }

  @Override
  public boolean visitOptionElement(OptionElement oe){
    searchAndReplace(oe.getSubElements());
    return true;
  }
}
