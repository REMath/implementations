package hampi;

import hampi.constraints.*;

import java.util.Set;

/**
 * Common class for solver implementations.
 */
public abstract class AbstractSolver{

  private final String name;
  public boolean verbose = false;

  public AbstractSolver(String name){
    this.name = name;
  }

  /**
   * Find and return the solution. size is the size of the variable (in
   * characters).
   */
  public abstract Solution solve(Constraint c, int size);

  /**
   * Check that no subsequence result should be outside the length of the
   * solution Should not happen when using the Hampi parser, but can happen when
   * creating the constraints using the Java API.
   *
   */
  protected boolean isValidSubsequencesLength(Constraint c, int size){
    for (Constraint conjunct : c.getConjuncts()){
      Set<SubsequenceExpression> subsequences = conjunct.getSubsequenceVals();
      for (SubsequenceExpression sub : subsequences){
        if (!sub.isValid(size))
          return false;
      }
    }
    return true;
  }

  /**
   * Returns the name of the solver.
   */
  public final String getName(){
    return name;
  }

  @Override
  public String toString(){
    return getName();
  }
}
