package hampi.constraints;

import hampi.Solution;

import java.util.*;

public class SubsequenceExpression extends Expression{
  private final VariableExpression expr;
  private final int fromIndex;
  private final int len;

  public SubsequenceExpression(VariableExpression expr, int fromIndex, int len){
    super(ElementKind.SUBSEQUENCE_EXPRESSION);
    this.expr = expr;
    this.fromIndex = fromIndex;
    this.len = len;
  }

  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof SubsequenceExpression))
      return false;
    SubsequenceExpression that = (SubsequenceExpression) obj;
    return that.expr.equals(this.expr) && that.fromIndex == this.fromIndex && that.len == this.len;
  }

  @Override
  public String getValue(Solution solution){
    return expr.getValue(solution).substring(fromIndex, fromIndex + len);
  }

  @Override
  public Set<VariableExpression> getVariables(){
    return expr.getVariables();
  }

  @Override
  public Set<SubsequenceExpression> getSubsequenceVals(){
    return Collections.singleton(this);
  }

  @Override
  public int hashCode(){
    return expr.hashCode() + 7 * (fromIndex + len);
  }

  @Override
  public String toJavaCode(String hampiVar){
    return hampiVar + ".subsequenceExpr(\"" + expr.toJavaCode(hampiVar) + "," + fromIndex + "," + len + "\")";
  }

  @Override
  public String toString(){
    return expr.toString() + "[" + fromIndex + "," + len + "]";
  }

  @Override
  public void accept(ConstraintGrammarVisitor visitor){
    expr.accept(visitor);
    visitor.visitSubsequenceExpression(this);
  }

  public int getLength(){
    return len;
  }

  public int getStartIndex(){
    return fromIndex;
  }

  public boolean isValid(int size){
    return len + fromIndex <= size;
  }

  @Override
  public int getSize(int varSize){
    return len;
  }

  @Override
  public List<Integer> getVarOffSets(int varLen){
    return Collections.emptyList();
  }

  @Override
  public List<Integer> getSubsequenceOffSets(SubsequenceExpression val, int varLen){
    if (val.equals(this))
      return Collections.singletonList(0);
    else return  Collections.emptyList();
  }

}
