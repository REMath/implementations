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

import java.util.*;

/**
 * A concatenation regular expression.
 */
public final class ConcatRegexp extends Regexp{

  private final Regexp[] exps;
  private transient int  cachedLowerBound = -1;
  private transient int  cachedUpperBound = -1;

  private final int      cachedHashCode;

  ConcatRegexp(Regexp... exps){
    super(ElementKind.CONCAT_REGEXP);
    if (exps == null || exps.length < 2)
      throw new IllegalArgumentException("too few elements");
    this.exps = exps;
    this.cachedHashCode = 17 * Arrays.hashCode(exps);
  }

  ConcatRegexp(List<Regexp> rexpsInNewMain){
    this(rexpsInNewMain.toArray(new Regexp[rexpsInNewMain.size()]));
  }

  public Regexp[] getExpressions(){
    return exps;
  }

  @Override
  public boolean equals(Object obj){
    return obj instanceof ConcatRegexp && Arrays.equals(((ConcatRegexp) obj).exps, this.exps);
  }

  @Override
  public int hashCode(){
    return cachedHashCode;
  }

  @Override
  public String toString(){
    StringBuilder b = new StringBuilder();
    b.append("[");
    for (int i = 0; i < exps.length; i++){
      if (i != 0){
        b.append(" . ");
      }
      b.append(exps[i].toString());
    }
    b.append("]");
    return b.toString();
  }

  @Override
  public void accept(ConstraintGrammarVisitor v){
    for (Regexp exp : exps){
      exp.accept(v);
    }
    v.visitConcat(this);
  }

  @Override
  public String toJavaRegexpPattern(){
    StringBuilder b = new StringBuilder();
    for (Regexp e : exps){
      b.append("(").append(e.toJavaRegexpPattern()).append(")");
    }
    return b.toString();
  }

  @Override
  public String toJavaCode(String hampiVar){
    StringBuilder b = new StringBuilder();
    b.append(hampiVar + ".concatRegexp(");
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
    int sum = 0;
    for (Regexp e : exps){
      int low = e.getSizeLowerBound();
      if (low == Integer.MAX_VALUE){
        cachedLowerBound = low;
        return low; //not going to get any larger so just return
      }else{
        sum += low;
      }
    }
    cachedLowerBound = sum;
    return sum;
  }

  @Override
  public int getSizeUpperBound(){
    if (cachedUpperBound != -1)
      return cachedUpperBound;
    int sum = 0;
    for (Regexp e : exps){
      int high = e.getSizeUpperBound();
      if (high == Integer.MAX_VALUE){
        cachedUpperBound = high;
        return high;//not going to get any larger so just return
      }else{
        sum += high;
      }
    }
    cachedUpperBound = sum;
    return sum;
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
    Set<Character> result = new LinkedHashSet<Character>();
    for (Regexp r : exps){
      result.addAll(r.getAlphabetLowerbound());
    }
    return result;
  }
}
