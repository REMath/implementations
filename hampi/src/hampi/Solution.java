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
package hampi;

import hampi.constraints.*;
import hampi.parser.HProgram;

import java.util.*;

/**
 * Describes the solution to the constraint problem, i.e., gives assignments to
 * variables.
 */
public final class Solution{

  /**
   * Creates the solution that describes an UNSAT solution.
   */
  public static final Solution createUNSAT(){
    return new Solution(false);
  }

  /**
   * Creates the solution that describes a SAT solution. The caller can then set
   * the variable assignment.
   */
  public static final Solution createSAT(){
    return new Solution(true);
  }

  /**
   * Is this solution a SAT?
   */
  private final boolean                         isSAT;
  private final Map<VariableExpression, String> assignment;

  private Solution(boolean sat){
    this.isSAT = sat;
    this.assignment = new LinkedHashMap<VariableExpression, String>(1);
  }

  /**
   * Returns the value of the expression given this assignment for variables.
   */
  public String getValue(Expression e){
    return e.getValue(this);
  }

  /**
   * Returns the value assigned to the variable.
   */
  public String getValueForVar(VariableExpression var){
    if (!assignment.containsKey(var))
      throw new IllegalArgumentException("unbound variable " + var);
    return assignment.get(var);
  }

  /**
   * Returns the value assigned to the variable.
   */
  public String getValueForVar(String varName){
    return getValue(HampiConstraints.varExpr(varName));
  }

  /**
   * Sets the value assignment. The previous assignment is removed.
   */
  public void setValue(VariableExpression ve, String val){
    assert isSatisfiable() : "can't set values in UNSAT solutions";
    assignment.put(ve, val);
  }

  /**
   * Returns the variables with assigned values.
   */
  public Set<VariableExpression> getVariables(){
    return assignment.keySet();
  }

  /**
   * Returns whether this solution is for a satisfiable problem.
   */
  public boolean isSatisfiable(){
    return isSAT;
  }

  /**
   * Replace single characters with char codes
   */
  private String escape(String in) {
      StringBuffer sb = new StringBuffer();
      for (int i = 0; i < in.length(); i ++) {
	  sb.append("\\");
	  sb.append((int)in.charAt(i));
      }
      return sb.toString();
  }

  /**
   * Pretty-print assignment
   */
  private String assignmentToString() {
      StringBuffer sb = new StringBuffer();
      sb.append("{");
      for (VariableExpression ve : this.assignment.keySet()) {
	  String value = this.assignment.get(ve);
	  sb.append(ve.toString());
	  sb.append("=\"");
	  sb.append(escape(value));
	  sb.append("\" (" + value.length() + ")\n");
      }
      sb.append("}");
      return sb.toString();
  }

  @Override
  public String toString() {
      boolean printord = HampiOptions.INSTANCE.get("printOrd").equals("yes");
      if (!isSatisfiable())
        return "UNSAT";
      else if (printord)
        return assignmentToString();
      else
        return this.assignment.toString();
  }

  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof Solution))
      return false;
    Solution that = (Solution) obj;
    return this.isSAT == that.isSAT && this.assignment.equals(that.assignment);
  }

  @Override
  public int hashCode(){
    return Boolean.valueOf(isSAT).hashCode() * assignment.hashCode();
  }

  /**
   * Checks whether this solution is valid for the given constraint.
   */
  public boolean isValidFor(Constraint constr){
    return new SolutionChecker().checkSolution(constr, this);
  }

  /**
   * Checks whether this solution is valid.
   */
  public boolean isValidFor(HProgram prog, Hampi hampi){
    return new SolutionChecker().checkSolution(prog, hampi, this);
  }
}