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

import hampi.Hampi;
import hampi.constraints.*;
import hampi.grammars.*;
import hampi.utils.*;

import java.util.*;

/**
 * Given a grammar and a length, generates a regular expression that describes
 * all strings in the grammar and of the given length.
 */
public class GrammarStringBounder{
  private boolean terms_are_single_char;//each terminal counts as 1 character?
  private final StopWatch distroTimer = new StopWatch("distributions in bounding");
  private final PigeonHoleDistributor distributor = new PigeonHoleDistributor();

  /**
   * Returns the regular expression that describes all strings of the given size
   * derivable from the given nonterminal or null if no such string exists.<br>
   * <br>
   * The last option specifies whether each terminal counts as 1 character
   * (e.g., a token), or terminals contribute all chars in their name.
   */
  public Regexp getBoundedRegexp(Grammar g, String startSymbol, int bound, boolean oneCharTerminals){
    terms_are_single_char = oneCharTerminals;
    new EpsilonProductionRemover().removeEpsilonProductions(g, startSymbol);//in-place
    new UselessProductionCycleRemover().remove(g, startSymbol);//in-place
    bounds = new GeneratableStringCounter().getBounds(g, oneCharTerminals);
    Regexp result = internalGetBoundedRegexp(g, startSymbol, bound);
    System.out.println(distroTimer);
    return result;
  }

  private Map<GrammarElement, Integer>                                            bounds;

  private final DoubleKeyMap<String, Integer, Regexp>                             regexpCache = new DoubleKeyMap<String, Integer, Regexp>();

  private Regexp internalGetBoundedRegexp(Grammar g, String startSymbol, int bound){
    if (regexpCache.containsKeys(startSymbol, bound))
      return regexpCache.get(startSymbol, bound);

    //removing epsilons may not succeed for start symbol. We check if that's the case.
    boolean canGenerateEmptyString = g.containsEpsilonProduction(startSymbol);

    List<Regexp> x = new ArrayList<Regexp>();
    for (GrammarProduction prod : g.getRule(startSymbol).getProductions()){
      List<GrammarProductionElement> elems = prod.getElements();
      if (canGenerateEmptyString || elems.size() <= bound){//uses the fact that every symbol (other than start) produces at least one terminal
        List<List<Integer>> distros = new ArrayList<List<Integer>>(distributions(bound, elems));

        distrosLoop: for (int j = 0; j < distros.size(); j++){
          List<Integer> distro = distros.get(j);
          Regexp[] exps = new Regexp[distro.size()];
          for (int i = 0; i < elems.size(); i++){
            GrammarProductionElement elem = elems.get(i);
            int sizeForElem = distro.get(i);
            if (terms_are_single_char){
              if (sizeForElem > 1 && (elem.getKind() == GrammarElementKind.GTERMINAL || elem.getKind() == GrammarElementKind.GSPECIAL)){
                continue distrosLoop;//no way you can generate a string longer than 1 from a terminal
              }
              if (sizeForElem == 1 && elem.getKind() == GrammarElementKind.GTERMINAL){
                TerminalElement te = (TerminalElement) elem;
                exps[i] = HampiConstraints.constRegexp(te.getNameNoQuotes());
              }else if (sizeForElem == 1 && elem.getKind() == GrammarElementKind.GSPECIAL){
                SpecialElement spec = (SpecialElement) elem;
                exps[i] = HampiConstraints.constRegexp(spec.getNameNoDelimiters());
              }else if (elem.getKind() == GrammarElementKind.GNONTERMINAL){
                NonterminalElement nt = (NonterminalElement) elem;
                if (bounds.containsKey(nt) && bounds.get(nt) < sizeForElem){//cannot generate a string longer than the upper bound on all strings generatable from the nonterminal
                  continue distrosLoop;
                }
                Regexp subRegexp = internalGetBoundedRegexp(g, nt.getName(), sizeForElem);
                if (subRegexp != null){
                  exps[i] = subRegexp;
                }else{
                  continue distrosLoop;
                }
              }else
                throw new IllegalStateException("expected a nonterminal or special" + elem);
            }else{
              if (elem.getKind() == GrammarElementKind.GSPECIAL)
                throw new UnsupportedOperationException("not implemented yet");
              if (elem.getKind() == GrammarElementKind.GTERMINAL){
                TerminalElement term = (TerminalElement) elem;
                if (term.getNameNoQuotes().length() != sizeForElem){
                  continue distrosLoop;//no way you can generate a string this long
                }else{
                  exps[i] = HampiConstraints.constRegexp(term.getNameNoQuotes());
                }
              }else if (elem.getKind() == GrammarElementKind.GNONTERMINAL){
                NonterminalElement nt = (NonterminalElement) elem;
                if (bounds.containsKey(nt) && bounds.get(nt) < sizeForElem){//cannot generate a string longer than the upper bound on all strings generatable from the nonterminal
                  continue distrosLoop;
                }
                Regexp subRegexp = internalGetBoundedRegexp(g, nt.getName(), sizeForElem);
                if (subRegexp != null){
                  exps[i] = subRegexp;
                }else{
                  continue distrosLoop;
                }
              }else
                throw new IllegalStateException("expected a nonterminal or special" + elem);
            }
          }
          Regexp e;
          if (exps.length == 1){
            e = exps[0];
          }else{
            e = HampiConstraints.concatRegexp(exps);
          }
          if (!x.contains(e)){
            x.add(e);
          }
        }
      }
    }

    Regexp result;
    if (x.isEmpty() && !canGenerateEmptyString){
      result = null;
    }else if (x.isEmpty() && canGenerateEmptyString){
      Hampi h = new Hampi();
      result = h.constRegexp("");
    }else if (x.size() == 1){
      result = x.get(0);
    }else{
      Hampi h = new Hampi();
      result = h.orRegexp(x.toArray(new Regexp[x.size()]));
    }
    regexpCache.put(startSymbol, bound, result);
    return result;
  }

  private Set<List<Integer>> distributions(int bound, List<GrammarProductionElement> elems){
    distroTimer.start();
    int sumSize = elems.size();
    List<Integer> lowerBounds = lowerBounds(elems, bound);
    List<Integer> upperBounds = upperBounds(elems, bound, lowerBounds);
    Set<List<Integer>> result = distributor.distribute2(sumSize, bound, lowerBounds, upperBounds);
    distroTimer.stop();
    return result;
  }

  private List<Integer> lowerBounds(List<GrammarProductionElement> elems, int bound){
    List<Integer> lowerBounds = new ArrayList<Integer>(elems.size());
    for (GrammarProductionElement grammarProductionElement : elems){
      if (grammarProductionElement.getKind() == GrammarElementKind.GTERMINAL){
        if (terms_are_single_char){
          lowerBounds.add(1);
        }else{
          TerminalElement term = (TerminalElement) grammarProductionElement;
          lowerBounds.add(term.getNameNoQuotes().length());
        }
      }else{
        boolean canBeEmpty = grammarProductionElement.getKind() == GrammarElementKind.GNONTERMINAL
            && grammarProductionElement.getGrammar().containsEpsilonProduction(grammarProductionElement.toString());
        lowerBounds.add(canBeEmpty ? 0 : 1);
      }
    }
    return lowerBounds;
  }

  private int sumSize(Collection<GrammarProductionElement> elems){
    return elems.size();
  }

  private List<Integer> upperBounds(List<GrammarProductionElement> elems, int bound, List<Integer> lowerBounds){
    List<Integer> upperBounds = new ArrayList<Integer>(elems.size());
    for (int i = 0; i < elems.size(); i++){
      GrammarProductionElement grammarProductionElement = elems.get(i);
      int upperBound;
      if (grammarProductionElement.getKind() == GrammarElementKind.GTERMINAL){
        if (terms_are_single_char){
          upperBound = 1;
        }else{
          TerminalElement term = (TerminalElement) grammarProductionElement;
          upperBound = term.getNameNoQuotes().length();
        }
      }else{
        //      upperBound= bound - (size - 1);//TODO still too conservative: use the 'bounds' map
        upperBound = bound;
      }
      upperBounds.add(Math.max(upperBound, lowerBounds.get(i)));
    }
    return upperBounds;
  }

  //repeates the num element n times
  private static List<Integer> copy(int num, int times){
    Integer[] ints = new Integer[times];
    Arrays.fill(ints, num);
    return Arrays.asList(ints);
  }
}
