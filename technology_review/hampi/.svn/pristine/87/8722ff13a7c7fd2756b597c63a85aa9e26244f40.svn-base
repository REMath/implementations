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

import hampi.utils.ASCIITable;

import java.util.*;

/**
 * A constant regular expression.
 */
public final class ConstRegexp extends Regexp{
  /* These symbols need to be escaped when creating Java regexp */
  private static final char[] SPECIALS = { '(', ')', '*', '-', '+', '?', '[', '{', '^', '|' };
  static{
    Arrays.sort(SPECIALS);//prep for binary search
  }
  private final String        str;
  private final int           cachedHashCode;

  ConstRegexp(String str){
    super(ElementKind.CONST_REGEXP);
    if (str == null)
      throw new IllegalArgumentException("bad argument " + str);
    this.str = str;
    this.cachedHashCode = 19 * str.hashCode();
  }

  public static Regexp[] createRange(char start, char end){
    if (start > end)
      throw new IllegalArgumentException("invalid parameter");
    Regexp[] result = new Regexp[end - start + 1];
    for (int i = start; i <= end; i++){
      result[i - start] = new ConstRegexp(String.valueOf(ASCIITable.asciiChar(i)));
    }
    return result;
  }

  public static Regexp[] createSet(Set<Character> chars){
    Set<Regexp> result = new LinkedHashSet<Regexp>(chars.size());
    for (Character c : chars){
      result.add(new ConstRegexp(new String(new char[] { c })));
    }
    return result.toArray(new Regexp[result.size()]);
  }

  @Override
  public boolean equals(Object obj){
    return obj instanceof ConstRegexp && ((ConstRegexp) obj).str.equals(this.str);
  }

  @Override
  public int hashCode(){
    return cachedHashCode;
  }

  @Override
  public String toString(){
    return str;
  }

  @Override
  public void accept(ConstraintGrammarVisitor v){
    v.visitConst(this);
  }

  public String getString(){
    return str;
  }

  @Override
  public String toJavaRegexpPattern(){
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < str.length(); i++){
      char c = str.charAt(i);
      b.append(escape(c));
    }
    return b.toString();
  }

  private String escape(char c){
    if (Arrays.binarySearch(SPECIALS, c) >= 0)
      return "\\" + c;
    else
      return String.valueOf(c);
  }

  @Override
  public String toJavaCode(String hampiVar){
    return hampiVar + ".constRegexp(\"" + str + "\")";
  }

  @Override
  public int getSizeLowerBound(){
    return str.length();
  }

  @Override
  public int getSizeUpperBound(){
    return str.length();
  }

  @Override
  public Set<Character> getUsedCharacters(){
    Set<Character> result = new LinkedHashSet<Character>(str.length());
    for (char c : str.toCharArray()){
      result.add(c);
    }
    return result;
  }

  @Override
  public Set<Character> getAlphabetLowerbound(){
    Set<Character> result = new LinkedHashSet<Character>(str.length());
    for (Character ch : str.toCharArray()){
      result.add(ch);
    }
    return result;
  }

  public boolean isEmpty(){
    return str.isEmpty();
  }
}
