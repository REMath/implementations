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

/**
 * A common superclass for all visitors. Subclasses may override just the
 * methods they need.
 */
public abstract class ConstraintGrammarVisitor{
  //----------- regexp

  public void visitConst(ConstRegexp c){
    // empty
  }

  public void visitConcat(ConcatRegexp c){
    // empty
  }

  public void visitOr(OrRegexp c){
    // empty
  }

  public void visitStar(StarRegexp c){
    // empty
  }

  //----------- constraints

  public void visitRegexpConstraint(RegexpConstraint c){
    //empty
  }

  public void visitAndConstraint(AndConstraint c){
    //empty
  }

  //----------- expressions

  public void visitConcatExpression(ConcatExpression c){
    //empty
  }

  public void visitConstantExpression(ConstantExpression c){
    //empty
  }

  public void visitVariableExpression(VariableExpression c){
    //empty
  }

  public void visitSubsequenceExpression(SubsequenceExpression subsequenceExpression){
    // empty
  }

  public void visitEqualsConstraint(EqualsConstraint equalsConstraint){
    // empty

  }

}
