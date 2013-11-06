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
 * A regular language constraint: expr in Regexp.
 */
public final class RegexpConstraint extends Constraint{

  private final Expression expr;
  private final Regexp     regexp;
  private final boolean    membership;

  RegexpConstraint(Expression expr, boolean membership, Regexp regexp){
    super(ElementKind.REGEXP_CONSTRAINT);
    assert expr != null;
    assert regexp != null;

    this.expr = expr;
    this.membership = membership;
    this.regexp = regexp;
  }

  /**
   * Returns the lhs expression.
   */
  public Expression getExpression(){
    return expr;
  }

  /**
   * Returns the regular expression from this constraint.
   */
  public Regexp getRegexp(){
    return regexp;
  }

  /**
   * Returns whether this constraint is a membeship or non-membership
   * constraint.
   */
  public boolean isMembership(){
    return membership;
  }

  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof RegexpConstraint))
      return false;
    RegexpConstraint that = (RegexpConstraint) obj;
    return that.expr.equals(this.expr) && this.membership == that.membership && that.regexp.equals(this.regexp);
  }

  @Override
  public int hashCode(){
    return 3 * expr.hashCode() * (17 + Boolean.valueOf(membership).hashCode()) * regexp.hashCode();
  }

  @Override
  public String toString(){
    return expr.toString() + (membership ? " in " : " notin ") + regexp.toString();
  }

  @Override
  public List<Constraint> getConjuncts(){
    return Collections.<Constraint>singletonList(this);
  }

  @Override
  public Set<VariableExpression> getVariables(){
    return expr.getVariables();
  }

  @Override
  public Set<SubsequenceExpression> getSubsequenceVals(){
    return expr.getSubsequenceVals();
  }

  @Override
  public void accept(ConstraintGrammarVisitor visitor){
    expr.accept(visitor);
    regexp.accept(visitor);
    visitor.visitRegexpConstraint(this);
  }

  @Override
  public String toJavaCode(String hampiVar){
    StringBuilder b = new StringBuilder();
    b.append(hampiVar + ".regexpConstraint(");
    b.append(expr.toJavaCode(hampiVar));
    b.append(", ");
    b.append(String.valueOf(membership));
    b.append(", ");
    b.append(regexp.toJavaCode(hampiVar));
    b.append(")");
    return b.toString();
  }

  @Override
  public Set<Character> alphabetLowerbound(){
    return getRegexp().getAlphabetLowerbound();
  }

  @Override
  public boolean isLegal(int varSize){
    if (!isMembership())
      return true;
    int expressionSize = getExpression().getSize(varSize);
    return getRegexp().getSizeUpperBound() >= expressionSize && getRegexp().getSizeLowerBound() <= expressionSize;
  }

  @Override
  public void removeUnequalSizeEqualities(int varLength){
  }
}