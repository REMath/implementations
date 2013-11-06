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

import java.util.Set;

/**
 * A regular expression.
 */
public abstract class Regexp{
  private final ElementKind kind;

  Regexp(ElementKind kind){
    this.kind = kind;
  }

  public final ElementKind getKind(){
    return kind;
  }

  @Override
  public abstract boolean equals(Object obj);

  @Override
  public abstract int hashCode();

  @Override
  public abstract String toString();

  /**
   * Visitor pattern.
   */
  public abstract void accept(ConstraintGrammarVisitor v);

  /**
   * Returns the regexp in the syntax understandable for Java string matching.
   * 
   * @see String#matches(String)
   */
  public abstract String toJavaRegexpPattern();

  /**
   * Returns whether or not the given string matches this expression.
   */
  public final boolean matches(String string){
    return string.matches(toJavaRegexpPattern());
  }

  /**
   * Returns the Java code that creates this regexp. Very useful for debugging.
   */
  public abstract String toJavaCode(String hampiVar);

  /**
   * Returns the upper bound on the size of strings described by this regexp.
   * (i.e., a number that is larger or equal to the length of the longest string
   * described by this regexp) Return Integer.MAX_INTEGER if no bound exists.
   */
  public abstract int getSizeUpperBound();

  /**
   * Returns the lower bound on the size of strings described by this regexp
   * (i.e., a number that is smaller or equal to the length of the shortest
   * string described by this regexp)
   */
  public abstract int getSizeLowerBound();

  /**
   * Returns the set of characters that are certain to appear in <em>every</em>
   * string described by this regexp.
   */
  public abstract Set<Character> getAlphabetLowerbound();

  /**
   * Returns the set of characters used in this regexp.
   */
  public abstract Set<Character> getUsedCharacters();

}
