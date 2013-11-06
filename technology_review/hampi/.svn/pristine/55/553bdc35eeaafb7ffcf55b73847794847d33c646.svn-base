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

import hampi.Solution;

import java.util.*;

/**
 * Represents an expression used in the constraints.
 */
public abstract class Expression{
  private final ElementKind kind;

  Expression(ElementKind kind){
    this.kind = kind;
  }

  public final ElementKind getKind(){
    return kind;
  }

  @Override
  public abstract String toString();

  @Override
  public abstract int hashCode();

  @Override
  public abstract boolean equals(Object obj);

  /**
   * Returns the set of variables used in this expression.
   */
  public abstract Set<VariableExpression> getVariables();

  /**
   * Visitor pattern.
   */
  public abstract void accept(ConstraintGrammarVisitor visitor);

  /**
   * Returns the value of this expression given the assignment of values to
   * variables.
   */
  public abstract String getValue(Solution solution);

  /**
   * Returns Java code that creates this expression.
   */
  public abstract String toJavaCode(String hampiVar);

  /**
   * Returns the set of variables used in this expression.
   */
  public abstract Set<SubsequenceExpression> getSubsequenceVals();

  /**
   * Returns the size of the expression under a substitution with variable on
   * length varLength
   */
  public abstract int getSize(int varLength);

  /**
   * Returns the offset of the variable (in terms of chars).
   *
   */
  public abstract List<Integer> getVarOffSets(int varLen);

  /**
   * Returns the offset of the subsequence value (in terms of chars).
   *
   */
  public abstract List<Integer> getSubsequenceOffSets(SubsequenceExpression val, int varLen);
}
