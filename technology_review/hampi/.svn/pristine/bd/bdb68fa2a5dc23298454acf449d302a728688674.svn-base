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
 * Represents a concatenation expression.
 */
public final class ConcatExpression extends Expression{

  private final List<Expression> subexpressions;

  ConcatExpression(Expression... expressions){
    this(Arrays.asList(expressions));
  }

  ConcatExpression(List<Expression> expressions){
    super(ElementKind.CONCAT_EXPRESSION);
    this.subexpressions = expressions;
  }

  public List<Expression> getSubexpressions(){
    return subexpressions;
  }

  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof ConcatExpression))
      return false;
    ConcatExpression that = (ConcatExpression) obj;
    return that.subexpressions.equals(this.subexpressions);
  }

  @Override
  public int hashCode(){
    return subexpressions.hashCode();
  }

  @Override
  public String toString(){
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < subexpressions.size(); i++){
      if (i != 0){
        b.append(" . ");
      }
      b.append(subexpressions.get(i).toString());
    }
    return b.toString();
  }

  @Override
  public Set<VariableExpression> getVariables(){
    Set<VariableExpression> result = new LinkedHashSet<VariableExpression>();
    for (Expression expression : subexpressions){
      result.addAll(expression.getVariables());
    }
    return result;
  }

  @Override
  public Set<SubsequenceExpression> getSubsequenceVals(){
    Set<SubsequenceExpression> result = new LinkedHashSet<SubsequenceExpression>();
    for (Expression expression : subexpressions){
      result.addAll(expression.getSubsequenceVals());
    }
    return result;
  }

  @Override
  public void accept(ConstraintGrammarVisitor visitor){
    for (Expression e : subexpressions){
      e.accept(visitor);
    }
    visitor.visitConcatExpression(this);
  }

  @Override
  public String getValue(Solution solution){
    StringBuilder b = new StringBuilder();
    for (Expression sub : subexpressions){
      b.append(sub.getValue(solution));
    }
    return b.toString();
  }

  @Override
  public String toJavaCode(String hampiVar){
    StringBuilder b = new StringBuilder();
    b.append(hampiVar + ".concatExpr(");
    for (int i = 0; i < subexpressions.size(); i++){
      if (i != 0){
        b.append(", ");
      }
      b.append(subexpressions.get(i).toJavaCode(hampiVar));
    }
    b.append(")");
    return b.toString();
  }

  @Override
  public int getSize(int varSize){
    int sum = 0;
    for (Expression e : subexpressions){
      sum += e.getSize(varSize);
    }
    return sum;
  }

  @Override
  public List<Integer> getVarOffSets(int varLen){
    int constLen = 0;
    List<Integer> offsets = new ArrayList<Integer>();
    for (Expression sub : subexpressions){
      if (sub.getKind() == ElementKind.CONST_EXPRESSION){
        ConstantExpression constExpr = (ConstantExpression) sub;
        String str = constExpr.getString();
        constLen += str.length();
      }
      if (sub.getKind() == ElementKind.VAR_EXPRESSION){
        offsets.add(constLen);
        constLen += varLen;
      }
      if (sub.getKind() == ElementKind.SUBSEQUENCE_EXPRESSION){
        constLen += ((SubsequenceExpression) sub).getLength();
      }
      if (sub.getKind() == ElementKind.CONCAT_EXPRESSION)
        throw new IllegalArgumentException("should not have nested concats: " + this);
    }
    return offsets;
  }

  @Override
  public List<Integer> getSubsequenceOffSets(SubsequenceExpression val, int varLen){
    int constLen = 0;
    List<Integer> offsets = new ArrayList<Integer>();
    for (Expression sub : subexpressions){
      if (sub.getKind() == ElementKind.CONST_EXPRESSION){
        ConstantExpression constExpr = (ConstantExpression) sub;
        String str = constExpr.getString();
        constLen += str.length();
      }
      if (sub.getKind() == ElementKind.VAR_EXPRESSION){
        constLen += varLen;
      }
      if (sub.getKind() == ElementKind.SUBSEQUENCE_EXPRESSION){
        SubsequenceExpression subsequenceExpr = (SubsequenceExpression) sub;
        if (subsequenceExpr.equals(val)){
          offsets.add(constLen);
        }
        constLen += subsequenceExpr.getLength();
      }
      if (sub.getKind() == ElementKind.CONCAT_EXPRESSION)
        throw new IllegalArgumentException("should not have nested concats: " + this);
    }
    return offsets;
  }

}
