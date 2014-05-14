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
package hampi.constraints;

import hampi.utils.*;

import java.util.*;

import jpaul.DataStructs.ArraySet;

/**
 * A union regular expression.
 */
public final class OrRegexp extends Regexp{

  private final Regexp[] exps;
  private transient final boolean isSetOfCharacters;    //NOTE this is not part of the abstract state and is excluded from equals/hashCode
  private transient int  cachedLowerBound = -1;
  private transient int  cachedUpperBound = -1;

  OrRegexp(Regexp... exps){
    super(ElementKind.OR_REGEXP);
    if (exps == null || exps.length < 2)
      throw new IllegalArgumentException("invalid argument, too few args");
    this.exps = exps;
    this.isSetOfCharacters = isSetOfCharacters();
  }

  @Override
  public boolean equals(Object obj){
    return obj instanceof OrRegexp && Arrays.equals(((OrRegexp) obj).exps, this.exps);
  }

  @Override
  public int hashCode(){
    return 13 * Arrays.hashCode(exps);
  }

  @Override
  public String toString(){
    if (isSetOfCharacters){
      StringBuilder b = new StringBuilder();
      b.append("[");
      for (Pair<Character, Character> range : getCharacterRanges()){
        b.append(ASCIITable.isReadable(range.first) ? range.first : "C" + (int) range.first);
        b.append("-");
        b.append(ASCIITable.isReadable(range.second) ? range.second : "C" + (int) range.second);
      }
      b.append("]");
      return b.toString();
    }else{
      StringBuilder b = new StringBuilder();
      b.append("[");
      for (int i = 0; i < exps.length; i++){
        if (i != 0){
          b.append(" + ");
        }
        b.append(exps[i].toString());
      }
      b.append("]");
      return b.toString();
    }
  }

  @Override
  public void accept(ConstraintGrammarVisitor v){
    for (Regexp exp : exps){
      exp.accept(v);
    }
    v.visitOr(this);
  }

  public Regexp[] getExpressions(){
    return exps;
  }

  @Override
  public String toJavaRegexpPattern(){
    if (isSetOfCharacters){
      StringBuilder b = new StringBuilder();
      b.append("[");
      for (Pair<Character, Character> range : getCharacterRanges()){
        b.append(range.first);
        b.append("-");
        b.append(range.second);
      }
      b.append("]");
      return b.toString();
    }
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < exps.length; i++){
      if (i != 0){
        b.append("|");
      }
      b.append(exps[i].toJavaRegexpPattern());
    }
    return b.toString();
  }

  @Override
  public String toJavaCode(String hampiVar){
    StringBuilder b = new StringBuilder();
    b.append(hampiVar + ".orRegexp(");
    for (int i = 0; i < exps.length; i++){
      if (i != 0){
        b.append(", ");
      }
      b.append(exps[i].toJavaCode(hampiVar));
    }
    b.append(")");
    return b.toString();
  }

  @Override
  public int getSizeLowerBound(){
    if (cachedLowerBound != -1)
      return cachedLowerBound;
    int min = Integer.MAX_VALUE;
    for (Regexp e : exps){
      min = Math.min(min, e.getSizeLowerBound());
    }
    cachedLowerBound = min;
    return min;
  }

  @Override
  public int getSizeUpperBound(){
    if (cachedUpperBound != -1)
      return cachedUpperBound;
    int max = 0;
    for (Regexp e : exps){
      max = Math.max(max, e.getSizeUpperBound());
    }
    cachedUpperBound = max;
    return max;
  }

  /**
   * Returns whether this union expression represents the whole alphabet range,
   * e.g., [a-z]
   */
  public boolean isFullAlphabetRange(Set<Character> alphabet){
    Set<Regexp> exprSet = new ArraySet<Regexp>(exps);
    if (exprSet.size() != alphabet.size())
      return false;
    for (Regexp ex : exprSet){
      if (ex.getKind() != ElementKind.CONST_REGEXP)
        return false;
      ConstRegexp re = (ConstRegexp) ex;
      if (re.getString().length() != 1)
        return false;
      Character c = re.getString().charAt(0);//first and only char
      if (!alphabet.contains(c))//we checked sizes so it's enough to check onesided inclusion
        return false;
    }
    return true;
  }

  /**
   * Returns whether this expression is a list of ranges of characters.
   */
  public boolean isSetOfCharacters(){
    return getSubexpressionsAsChars() != null;
  }

  /**
   * Returns the characters as an array, or null if this is not a set of
   * characters.
   */
  public char[] getSubexpressionsAsChars(){
    char[] chars = new char[exps.length];
    for (int i = 0; i < exps.length; i++){
      Regexp re = exps[i];
      if (re.getKind() == ElementKind.CONST_REGEXP){
        ConstRegexp c = (ConstRegexp) re;
        if (c.getString().length() != 1)
          return null;
        else{
          chars[i] = c.getString().charAt(0);
        }
      }else
        return null;
    }
    return chars;
  }

  /**
   * Returns the list of pairs of lower, upper end of characters ranges. This is
   * for regexps such as [a-zA-Z]. Returns null if this expression is not a list
   * of character ranges.
   */
  public List<Pair<Character, Character>> getCharacterRanges(){
    char[] chars = getSubexpressionsAsChars();
    if (chars == null)
      return null;
    return CollectionsExt.ranges(chars);
  }

  @Override
  public Set<Character> getUsedCharacters(){
    Set<Character> result = new LinkedHashSet<Character>();
    for (Regexp re : exps){
      result.addAll(re.getUsedCharacters());
    }
    return result;
  }

  @Override
  public Set<Character> getAlphabetLowerbound(){
    Set<Set<Character>> sets = new LinkedHashSet<Set<Character>>();
    for (Regexp r : exps){
      Set<Character> lb = r.getAlphabetLowerbound();
      sets.add(lb);
      if (lb.isEmpty())
        return lb;//shortcut because we intersect at the end
    }
    return CollectionsExt.<Character>intersectionSets(sets);
  }
}
