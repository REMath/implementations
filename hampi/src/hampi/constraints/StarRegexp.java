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
 * A Kleene star regular expression.
 */
public final class StarRegexp extends Regexp{

  private final Regexp exp;

  StarRegexp(Regexp exp){
    super(ElementKind.STAR_REGEXP);
    this.exp = exp;
  }

  public Regexp getExpression(){
    return exp;
  }

  @Override
  public boolean equals(Object obj){
    return obj instanceof StarRegexp && (((StarRegexp) obj).exp).equals(this.exp);
  }

  @Override
  public int hashCode(){
    return exp.hashCode() * 7;
  }

  @Override
  public String toString(){
    return exp.toString() + "*";
  }

  @Override
  public void accept(ConstraintGrammarVisitor v){
    exp.accept(v);
    v.visitStar(this);
  }

  @Override
  public String toJavaRegexpPattern(){
    return "(" + exp.toJavaRegexpPattern() + ")" + "*";
  }

  @Override
  public String toJavaCode(String hampiVar){
    StringBuilder b = new StringBuilder();
    b.append(hampiVar + ".starRegexp(");
    b.append(exp.toJavaCode(hampiVar));
    b.append(")");
    return b.toString();
  }

  @Override
  public int getSizeLowerBound(){
    return 0;
  }

  @Override
  public int getSizeUpperBound(){
    if (exp.getSizeUpperBound() == 0)
      return 0;
    return Integer.MAX_VALUE;
  }

  @Override
  public Set<Character> getUsedCharacters(){
    return exp.getUsedCharacters();
  }

  @Override
  public Set<Character> getAlphabetLowerbound(){
    return Collections.emptySet();//no char is required in a star expression
  }

}
