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
import hampi.stp.STPSolver;
import hampi.utils.StopWatch;

import java.io.*;
import java.util.*;

import org.antlr.runtime.RecognitionException;

/**
 * This is a facade for the Hampi solver.
 */
public final class Hampi{

  private AbstractSolver solver;
  public boolean         validateSolution = true;
  public boolean         verbose          = false;

  public Hampi(){
    solver = new STPSolver();
  }

  /**
   * Returns the solver implementation used by Hampi.
   */
  public AbstractSolver getSolver(){
    return solver;
  }

  /**
   * Set the solver implementation.
   */
  public void setSolver(AbstractSolver solver){
    this.solver = solver;
  }

  //----------------------------------------------------------------------------
  // Construction methods
  //----------------------------------------------------------------------------

  /**
   * Creates an variable with the given name.
   */
  public VariableExpression varExpr(String name){
    return HampiConstraints.varExpr(name);
  }

  /**
   * Creates a constant.
   */
  public Expression constExpr(String value){
    return HampiConstraints.constExpr(value);
  }

  /**
   * Creates a concatenation expression.
   */
  public Expression concatExpr(Expression... exprs){
    return HampiConstraints.concatExpr(exprs);
  }

  /**
   * Creates a concatenation expression.
   */
  public Expression concatExpr(List<Expression> exprs){
    return HampiConstraints.concatExpr(exprs);
  }

  /**
   * Creates a subsequence expression
   */
  public Expression subsequenceExpr(VariableExpression expr, int fromIndex, int len){
    return HampiConstraints.subsequenceExpr(expr, fromIndex, len);
  }

  public Constraint equalsConstraint(Expression e1, boolean equals, Expression e2){
    return HampiConstraints.equalsConstraint(e1, equals, e2);
  }

  /**
   * Creates a conjunction of constraints.
   */
  public Constraint andConstraint(Constraint... constraints){
    return HampiConstraints.andConstraint(constraints);
  }

  /**
   * Creates a conjunction of constraints.
   */
  public Constraint andConstraint(List<Constraint> conjuncts){
    return HampiConstraints.andConstraint(conjuncts);
  }

  /**
   * Creates a regular-language constraint.
   */
  public Constraint regexpConstraint(Expression e1, boolean member, Regexp e2){
    return HampiConstraints.regexpConstraint(e1, member, e2);
  }

  /**
   * Creates a constant regular expression (i.e., the only string is the given
   * string).
   */
  public Regexp constRegexp(String str){
    return HampiConstraints.constRegexp(str);
  }

  /**
   * Creates a constant regular expression (i.e., the only string is the given
   * character).
   */
  public Regexp constRegexp(char ch){
    return constRegexp(String.valueOf(ch));
  }

  /**
   * Creates an OR regular expression.
   */
  public Regexp orRegexp(Regexp... exps){
    return HampiConstraints.orRegexp(exps);
  }

  /**
   * Creates an OR regular expression.
   */
  public Regexp orRegexp(List<Regexp> exps){
    Regexp[] arr = exps.toArray(new Regexp[exps.size()]);
    return orRegexp(arr);
  }

  /**
   * Creates a concatenation regular expression.
   */
  public Regexp concatRegexp(Regexp... exps){
    return HampiConstraints.concatRegexp(exps);
  }

  /**
   * Creates a concatenation regular expression.
   */
  public Regexp concatRegexp(List<Regexp> exps){
    return HampiConstraints.concatRegexp(exps);
  }

  /**
   * Creates a star regular expression.
   */
  public Regexp starRegexp(Regexp r){
    return HampiConstraints.starRegexp(r);
  }

  /**
   * Creates a plus regular expression.
   */
  public Regexp plusRegexp(Regexp r){
    return HampiConstraints.plusRegexp(r);
  }

  /**
   * Creates a regular expression that describes a set of characters (range
   * between a low and high, when the characters are represented as numbers).
   */
  public Regexp rangeRegexp(char low, char high){
    return HampiConstraints.rangeRegexp(low, high);
  }

  //-----------------------------------------------------------------------------
  // Solving methods
  //-----------------------------------------------------------------------------

  /**
   * Solves the constraint and returns the solution. The solution may be
   * 'unsatisfiable'. Parameter size is the size of the variable (in
   * characters). The solution is optionally verified (depending on
   * {@link #validateSolution} variable).
   */
  public Solution solve(Constraint c, int size){
    assert c != null;
    StopWatch sw = new StopWatch("Solving using " + solver.getName());
    if (verbose){
      System.out.println("Solving using " + solver.getName());
      sw.start();
    }
    Solution sol = solver.solve(c, size);
    if (verbose){
      sw.stop();
      System.out.println(sw);
    }

    if (validateSolution && sol.isSatisfiable()){
      assert sol.isValidFor(c) : "invalid solution:\n" + c + "\n" + sol;
    }
    return sol;
  }

  //---------------------------------------------------------------------------
  // Entry points
  //---------------------------------------------------------------------------

  /**
   * The main entry point. Usage: <file_name> [options]<br>
   *
   * options(separate by spaces)<br>
   * -c check solution (Hampi checks if the computed solution satisfies the
   * constraints)<br>
   * -v verbose<br>
   * -t:XX timeout in seconds<br>
   *
   * TODO The result is sent to stdout.<br>
   * Exit codes: (using exit codes complicates testing)
   * <ul>
   * <li>0 if SAT</li>,
   * <li>1 if UNSAT</li>,
   * <li>2 if parse or well-formedness error,</li>
   * <li>3 if usage error,</li>
   * <li>4 if timeout,</li>
   * <li>5 if internal error</li>
   * </ul>
   */
  public static void main(String[] args) throws Exception{
    try{
      run(args);
    }catch (HampiResultException e){
      System.out.println(e.getMessage());
      System.exit(e.getExitCode());
    }catch (ThreadDeath e){
      throw e;//let him through
    }catch (Throwable e){
      e.printStackTrace(System.err);
      System.exit(HampiResultException.CODE_INTERNAL_ERROR);
    }
  }

  public static void run(String[] args) throws HampiResultException,RecognitionException,IOException{
    if (args.length == 0)
      throw HampiResultException.usage("Usage: Hampi <filename> [timeout in seconds]");
    List<String> argList = Arrays.asList(args);
    String fileName = args[0];
    boolean check = argList.contains("-c");
    boolean verbose = argList.contains("-v");//XXX mostly ignored for now
    InputStream istream = new FileInputStream(fileName);

    run(check, verbose, istream);
  }

  public static Solution run(boolean check, boolean verbose, InputStream istream) throws IOException,RecognitionException{
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    StopWatch parseTimer = new StopWatch("parsing");
    parseTimer.start();
    HProgram parse = HProgramParser.parse(baos, istream);
    parseTimer.stop();
    if (verbose){
      System.out.println(parseTimer);
    }
    if (parse == null)
      throw HampiResultException.parse("Parse errors \n" + baos.toString());
    String errorMsg = HProgramParser.checkWellFormedness(parse);
    if (errorMsg != null)
      throw HampiResultException.parse("Errors in \n" + errorMsg);

    Hampi hampi = new Hampi();
    hampi.validateSolution = check;
    int sizeMin = parse.getVarSizeMin();
    int sizeMax = parse.getVarSizeMax();
    for(int size = sizeMin; size <= sizeMax; size++){
      try{
        Constraint c = new HConstraintPreparer(hampi, size).prepare(parse);
        assert c != null;
        if (verbose){
          //      System.out.println(parse);
          hampi.getSolver().verbose = verbose;
        }
        Solution solve = hampi.solve(c, size);
        if (verbose){
           System.out.println("solution for size " + size + " " + solve);
        }
        if (solve.isSatisfiable()){
           System.out.println(solve);
	   return solve;
        }
      }catch(HampiResultException e){
	  if (!e.isUnsat())
	   throw e;
      }
    }
    throw HampiResultException.unsat();
  }

}