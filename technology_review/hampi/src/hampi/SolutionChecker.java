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
import hampi.parser.*;

import java.util.*;

/**
 * Checks whether the solution satisfies the constraint. This is useful for
 * verifying the validity of solutions.
 * 
 * TODO move to constraint or to solution
 */
public final class SolutionChecker{
  public boolean checkSolution(Constraint c, Solution s){
    if (!s.isSatisfiable())
      return true;//XXX we can't know for sure
    switch (c.getKind()){
    case AND_CONSTRAINT:
      return checkSolutionAndConstraint((AndConstraint) c, s);
    case REGEXP_CONSTRAINT:
      return checkSolutionRegexpConstraint((RegexpConstraint) c, s);
    default:
      throw new IllegalArgumentException("not a valid constraint " + c);
    }
  }

  private boolean checkSolutionRegexpConstraint(RegexpConstraint c, Solution s){
    String string = s.getValue(c.getExpression());
    return c.isMembership() == satisfies(string, c.getRegexp());
  }

  private boolean satisfies(String string, Regexp regexp){
    return string.matches(regexp.toJavaRegexpPattern());
  }

  private boolean checkSolutionAndConstraint(AndConstraint c, Solution s){
    for (Constraint constr : c.getConstraints()){
      boolean sol = checkSolution(constr, s);
      if (!sol)
        return false;
    }
    return true;
  }

  //----------------------------
  public boolean checkSolution(HProgram prog, Hampi hampi, Solution s){
    if (!s.isSatisfiable())
      return true;//XXX we can't know for sure
    List<HStatement> statements = prog.getStatements(HGrammarElementKind.STMT_ASSERT);
    for (HStatement stmt : statements){
      HAssertStatement assertion = (HAssertStatement) stmt;
      boolean check = checkAssert(assertion, prog, hampi, s);
      if (!check)
        return false;
    }
    return true;
  }

  private boolean checkAssert(HAssertStatement assertion, HProgram prog, Hampi hampi, Solution s){
    HBooleanExpression boolExpr = assertion.getBooleanExpression();
    switch (boolExpr.getKind()){
    case BEXPR_CONTAINS: {
      return checkContains((HContainsExpression) boolExpr, prog, hampi, s);
    }
    case BEXPR_IN: {
      return checkIn((HInExpression) boolExpr, prog, hampi, s);
    }
    default:
      throw new IllegalArgumentException("invalid expression " + boolExpr);
    }
  }

  private boolean checkContains(HContainsExpression containsExpr, HProgram prog, Hampi hampi, Solution s){
    String string = containsExpr.getString();
    boolean contains = containsExpr.contains();
    String variableName = containsExpr.getVariableName();
    String variableValue = variableValue(prog, variableName, hampi, s);
    return variableValue.contains(string) == contains;
  }

  /**
   * returns the value of the variable given the solution
   */
  private String variableValue(HProgram prog, String variableName, Hampi hampi, Solution s){
    HStatement decl = prog.getDecl(variableName);
    if (decl == null)
      throw new IllegalStateException("unknown variable " + variableName);
    switch (decl.getKind()){
    case STMT_VARDECL: {
      return s.getValue(hampi.varExpr(variableName));
    }
    case STMT_VALDECL: {
      return s.getValue(getExpression((HValDeclStatement) decl, variableName, prog, hampi));
    }
    case STMT_REGDECL: {
      throw new IllegalStateException("no value for REG variables");
    }
    case STMT_CFG: {
      throw new IllegalStateException("no value for CFG variables");
    }
    default:
      throw new IllegalStateException("invalid decl " + decl);

    }
  }

  private Expression getExpression(HValDeclStatement valDeclStatement, String variableName, HProgram prog, Hampi hampi){
    return getExpression(valDeclStatement.getExpression(), prog, hampi);
  }

  private Expression getExpression(HExpression expression, HProgram prog, Hampi hampi){
    switch (expression.getKind()){
    case EXPR_VAR:
      return hampi.varExpr(((HVarReferenceExpression) expression).getName());
    case EXPR_CONST:
      return hampi.constExpr(((HConstantExpression) expression).getValue());
    case EXPR_CONCAT: {
      HConcatExpression concat = (HConcatExpression) expression;
      List<Expression> exprs = new ArrayList<Expression>();
      for (HExpression e : concat.getSubExpressions()){
        exprs.add(getExpression(e, prog, hampi));
      }
      return hampi.concatExpr(exprs);
    }
    case EXPR_SUBSEQUENCE: {
      HSubsequenceExpression ce = (HSubsequenceExpression) expression;
      HStatement decl = prog.getDecl(ce.getName());
      switch (decl.getKind()){
      case STMT_VARDECL: {
        HVarDeclStatement v = (HVarDeclStatement) decl;
        return hampi.subsequenceExpr(hampi.varExpr(v.getVarName()), ce.getStartIndex(), ce.getLength());
      }
      default:
        throw new IllegalStateException("invalid usage of variable reference " + ce.getName() + " \n" + prog);
      }
    }
    default:
      throw new IllegalStateException("invalid expressio " + expression);
    }
  }

  private boolean checkIn(HInExpression inExpr, HProgram prog, Hampi hampi, Solution s){
    // TODO Auto-generated method stub
    return false;
  }

}
