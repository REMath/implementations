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

import hampi.utils.Utils;

import java.util.*;

/**
 * A conjunction of constraints.
 */
public final class AndConstraint extends Constraint{

  private final Set<Constraint> constraints;

  AndConstraint(Constraint... constraints){
    this(Arrays.asList(constraints));
  }

  AndConstraint(Collection<Constraint> set){
    super(ElementKind.AND_CONSTRAINT);
    this.constraints = new LinkedHashSet<Constraint>(set);
  }

  public void addConjunct(Constraint c){
    constraints.add(c);
  }

  public Set<Constraint> getConstraints(){
    return constraints;
  }

  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof AndConstraint))
      return false;
    AndConstraint that = (AndConstraint) obj;
    return this.constraints.equals(that.constraints);
  }

  @Override
  public int hashCode(){
    return constraints.hashCode();
  }

  @Override
  public String toString(){
    StringBuilder b = new StringBuilder();
    for (Constraint c : constraints){
      b.append(c.toString());
      b.append(Utils.nl);
    }
    return b.toString();
  }

  @Override
  public List<Constraint> getConjuncts(){
    List<Constraint> result = new ArrayList<Constraint>();
    for (Constraint c : constraints){
      result.addAll(c.getConjuncts());
    }
    return result;
  }

  @Override
  public Set<VariableExpression> getVariables(){
    Set<VariableExpression> result = new LinkedHashSet<VariableExpression>();
    for (Constraint c : constraints){
      result.addAll(c.getVariables());
    }
    return result;
  }

  @Override
  public Set<SubsequenceExpression> getSubsequenceVals(){
    Set<SubsequenceExpression> result = new LinkedHashSet<SubsequenceExpression>();
    for (Constraint c : constraints){
      result.addAll(c.getSubsequenceVals());
    }
    return result;
  }

  @Override
  public void accept(ConstraintGrammarVisitor visitor){
    for (Constraint c : constraints){
      c.accept(visitor);
    }
    visitor.visitAndConstraint(this);
  }

  @Override
  public String toJavaCode(String hampiVar){
    StringBuilder b = new StringBuilder();
    b.append(hampiVar + ".andConstraint(");
    Constraint[] cArray = constraints.toArray(new Constraint[constraints.size()]);
    for (int i = 0; i < cArray.length; i++){
      if (i != 0){
        b.append(", ");
      }
      b.append(cArray[i].toJavaCode(hampiVar));
    }
    b.append(")");
    return b.toString();
  }

  @Override
  public Set<Character> alphabetLowerbound(){
    Set<Character> result = new LinkedHashSet<Character>();
    for (Constraint conjunct : getConjuncts()){
      result.addAll(conjunct.alphabetLowerbound());
    }
    return result;
  }

  @Override
  public boolean isLegal(int varSize){
    for (Constraint conjunct : getConjuncts()){
      if (!conjunct.isLegal(varSize))
        return false;
    }
    return true;
  }

  @Override
  public void removeUnequalSizeEqualities(int varLength){
    Iterator<Constraint> iter = constraints.iterator();
    while (iter.hasNext()){
      Constraint c = iter.next();
      c.removeUnequalSizeEqualities(varLength);
      if (c instanceof EqualsConstraint){
        EqualsConstraint ec = (EqualsConstraint) c;
        if (!ec.isEqual() && ec.getExpression1().getSize(varLength) != ec.getExpression2().getSize(varLength)){
          iter.remove();
        }
      }
    }
  }
}
