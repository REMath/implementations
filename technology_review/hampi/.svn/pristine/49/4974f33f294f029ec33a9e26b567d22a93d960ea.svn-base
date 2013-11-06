package hampi.constraints;

import hampi.utils.CollectionsExt;

import java.util.*;

public class EqualsConstraint extends Constraint{
  private final Expression lhsExpr;
  private final Expression rhsExpr;
  private final boolean equals;


  public EqualsConstraint(Expression lhsExpr, boolean equals, Expression rhsExpr){
    super(ElementKind.EQUALS_CONSTRAINT);
    assert lhsExpr != null;
    assert rhsExpr != null;

    this.lhsExpr = lhsExpr;
    this.equals = equals;
    this.rhsExpr = rhsExpr;
  }

  @Override
  public void accept(ConstraintGrammarVisitor visitor){
    lhsExpr.accept(visitor);
    rhsExpr.accept(visitor);
    visitor.visitEqualsConstraint(this);
  }

  @Override
  public Set<Character> alphabetLowerbound(){
    return Collections.emptySet();
  }

  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof EqualsConstraint))
      return false;
    EqualsConstraint that = (EqualsConstraint) obj;
    return that.lhsExpr.equals(this.lhsExpr) && this.equals == that.equals && that.rhsExpr.equals(this.rhsExpr);
  }

  /**
   * Returns the rhs expression.
   */
  public Expression getExpression2(){
    return rhsExpr;
  }

  /**
   * Returns the lhs expression.
   */
  public Expression getExpression1(){
    return lhsExpr;
  }

  /**
   * Returns whether this constraint is a equal or not-equal constraint.
   */
  public boolean isEqual(){
    return equals;
  }

  @Override
  public List<Constraint> getConjuncts(){
    return Collections.<Constraint>singletonList(this);
  }

  @Override
  public Set<VariableExpression> getVariables(){
    return CollectionsExt.union(lhsExpr.getVariables(), rhsExpr.getVariables());
  }

  @Override
  public Set<SubsequenceExpression> getSubsequenceVals(){
    return CollectionsExt.union(lhsExpr.getSubsequenceVals(), rhsExpr.getSubsequenceVals());
  }

  @Override
  public int hashCode(){
    return 3 * lhsExpr.hashCode() * (17 + Boolean.valueOf(equals).hashCode()) * rhsExpr.hashCode();
  }

  @Override
  public String toString(){
    return lhsExpr.toString() + (equals ? " = " : " != ") + rhsExpr.toString();
  }

  @Override
  public boolean isLegal(int varSize){
    return true;
  }

  @Override
  public String toJavaCode(String hampiVar){
    StringBuilder b = new StringBuilder();
    b.append(hampiVar + ".equalsConstraint(");
    b.append(lhsExpr.toJavaCode(hampiVar));
    b.append(", ");
    b.append(String.valueOf(equals));
    b.append(", ");
    b.append(lhsExpr.toJavaCode(hampiVar));
    b.append(")");
    return b.toString();
  }

  @Override
  public void removeUnequalSizeEqualities(int varLength){
  }

}
