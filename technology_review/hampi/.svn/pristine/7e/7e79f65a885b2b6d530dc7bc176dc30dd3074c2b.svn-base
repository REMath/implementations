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
 * A variable for which the solver tries to find a value.
 */
public final class VariableExpression extends Expression{
  private final String name;

  VariableExpression(String name){
    super(ElementKind.VAR_EXPRESSION);
    this.name = name;
  }

  public String getName(){
    return name;
  }

  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof VariableExpression))
      return false;
    VariableExpression that = (VariableExpression) obj;
    return that.name.equals(this.name);
  }

  @Override
  public int hashCode(){
    return name.hashCode();
  }

  @Override
  public String toString(){
    return "VAR(" + name + ")";
  }

  @Override
  public Set<VariableExpression> getVariables(){
    return Collections.singleton(this);
  }

  @Override
  public Set<SubsequenceExpression> getSubsequenceVals(){
    return Collections.emptySet();
  }

  @Override
  public void accept(ConstraintGrammarVisitor visitor){
    visitor.visitVariableExpression(this);
  }

  @Override
  public String getValue(Solution solution){
    return solution.getValueForVar(this);
  }

  @Override
  public String toJavaCode(String hampiVar){
    return hampiVar + ".varExpr(\"" + name + "\")";
  }

  @Override
  public int getSize(int varSize){
    return varSize;
  }

  @Override
  public List<Integer> getVarOffSets(int varLen){
    return Collections.singletonList(0);
  }

  @Override
  public List<Integer> getSubsequenceOffSets(SubsequenceExpression val, int varLen){
    return Collections.emptyList();
  }
}
