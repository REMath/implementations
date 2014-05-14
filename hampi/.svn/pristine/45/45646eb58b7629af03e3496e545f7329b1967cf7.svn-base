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
 * A constant.
 */
public final class ConstantExpression extends Expression{

  private final String str;

  ConstantExpression(String str){
    super(ElementKind.CONST_EXPRESSION);
    this.str = str;
  }

  public String getString(){
    return str;
  }

  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof ConstantExpression))
      return false;
    ConstantExpression that = (ConstantExpression) obj;
    return that.str.equals(this.str);
  }

  @Override
  public int hashCode(){
    return str.hashCode();
  }

  @Override
  public String toString(){
    return "CONST(" + str + ")";
  }

  @Override
  public Set<VariableExpression> getVariables(){
    return Collections.emptySet();
  }

  @Override
  public Set<SubsequenceExpression> getSubsequenceVals(){
    return Collections.emptySet();
  }

  @Override
  public void accept(ConstraintGrammarVisitor visitor){
    visitor.visitConstantExpression(this);
  }

  @Override
  public String getValue(Solution solution){
    return str;
  }

  @Override
  public String toJavaCode(String hampiVar){
    return hampiVar + ".constExpr(\"" + str + "\")";
  }

  @Override
  public int getSize(int varSize){
    return str.length();
  }

  @Override
  public List<Integer> getVarOffSets(int varLen){
    return Collections.emptyList();
  }

  @Override
  public List<Integer> getSubsequenceOffSets(SubsequenceExpression sub, int varLen){
    return Collections.emptyList();
  }

}
