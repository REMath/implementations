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
package hampi.tests;

import hampi.*;
import hampi.constraints.*;
import junit.framework.TestCase;

public class RegressionTests extends TestCase{

  public void testPattern() throws Exception{
    Regexp alert = HampiConstraints.constRegexp("(1)");
    String pattern = alert.toJavaRegexpPattern();
    System.out.println(pattern);
    assertTrue("(1)".matches(pattern));
  }

  public void testPatternSpecialSymbols() throws Exception{
    Regexp alert = HampiConstraints.constRegexp("*");
    String pattern = alert.toJavaRegexpPattern();
    System.out.println(pattern);
    assertTrue("*".matches(pattern));
  }

  public void testPatternSpecialSymbols2() throws Exception{
    Regexp alert = HampiConstraints.constRegexp("+");
    String pattern = alert.toJavaRegexpPattern();
    System.out.println(pattern);
    assertTrue("+".matches(pattern));
  }

  public void testPatternSpecialSymbols3() throws Exception{
    Regexp alert = HampiConstraints.constRegexp("{");
    String pattern = alert.toJavaRegexpPattern();
    System.out.println(pattern);
    assertTrue("{".matches(pattern));
  }

  public void testPatternSpecialSymbols4() throws Exception{
    Regexp alert = HampiConstraints.constRegexp("}");
    String pattern = alert.toJavaRegexpPattern();
    System.out.println(pattern);
    assertTrue("}".matches(pattern));
  }

  public void testPatternSpecialSymbols5() throws Exception{
    Regexp alert = HampiConstraints.constRegexp("]");
    String pattern = alert.toJavaRegexpPattern();
    System.out.println(pattern);
    assertTrue("]".matches(pattern));
  }

  public void testPatternSpecialSymbols6() throws Exception{
    Regexp alert = HampiConstraints.constRegexp("[");
    String pattern = alert.toJavaRegexpPattern();
    System.out.println(pattern);
    assertTrue("[".matches(pattern));
  }

  public void testPatternSpecialSymbols7() throws Exception{
    String s = "^";
    Regexp alert = HampiConstraints.constRegexp(s);
    String pattern = alert.toJavaRegexpPattern();
    System.out.println(pattern);
    assertTrue(s.matches(pattern));
  }

  public void testPatternSpecialSymbols8() throws Exception{
    String s = "|";
    Regexp alert = HampiConstraints.constRegexp(s);
    String pattern = alert.toJavaRegexpPattern();
    System.out.println(pattern);
    assertTrue(s.matches(pattern));
  }

  public void testSolution(){
    Hampi hs = new Hampi();
    Regexp alert = hs.constRegexp("(1)");
    Expression v1 = hs.varExpr("v1");
    Expression e = v1;
    Constraint mainConst = hs.regexpConstraint(e, true, alert);

    String pattern = alert.toJavaRegexpPattern();
    Solution s = Solution.createSAT();
    s.setValue((VariableExpression) v1, "(1)");
    boolean checkSolution = new SolutionChecker().checkSolution(mainConst, s);
    assertTrue(checkSolution);
  }

  public void testSolution2(){
    Hampi hs = new Hampi();
    Regexp alert = hs.constRegexp("()");
    Expression v1 = hs.varExpr("v1");
    Expression e = v1;
    Constraint mainConst = hs.regexpConstraint(e, true, alert);

    Solution s = Solution.createSAT();
    s.setValue((VariableExpression) v1, "()");
    boolean checkSolution = new SolutionChecker().checkSolution(mainConst, s);
    assertTrue(checkSolution);
  }

  public void testSolution3(){
    Hampi hs = new Hampi();
    Regexp alert = hs.constRegexp("(");
    Expression v1 = hs.varExpr("v1");
    Expression e = v1;
    Constraint mainConst = hs.regexpConstraint(e, true, alert);

    Solution s = Solution.createSAT();
    s.setValue((VariableExpression) v1, "(");
    System.out.println(mainConst);
    boolean checkSolution = new SolutionChecker().checkSolution(mainConst, s);
    assertTrue(checkSolution);
  }

  public void testDupPredicate1(){
    //CONST(ab) . VAR(v0) . CONST(aa) in [[a . b] . [a + b]]
    Hampi hs = new Hampi();
    Expression e1 = hs.concatExpr(hs.constExpr("ab"), hs.varExpr("v0"), hs.constExpr("aa"));
    Regexp r1 = hs.concatRegexp(hs.concatRegexp(hs.constRegexp("a"), hs.constRegexp("b")), hs.orRegexp(hs.constRegexp("a"), hs.constRegexp("b")));
    Constraint c1 = hs.regexpConstraint(e1, true, r1);
    Constraint[] cs = { c1 };
    Constraint c = hs.andConstraint(cs);
    hs.solve(c, 1);
  }

  public void testDupPredicate2() throws Exception{
    //[bb + aa]
    //[ba + aa]
    Hampi hs = new Hampi();
    Expression e1 = hs.varExpr("v0");
    Regexp r1 = hs.concatRegexp(hs.orRegexp(hs.constRegexp("bb"), hs.constRegexp("aa")), hs.orRegexp(hs.constRegexp("ba"), hs.constRegexp("ba")));
    Constraint c1 = hs.regexpConstraint(e1, true, r1);
    Constraint[] cs = { c1 };
    Constraint c = hs.andConstraint(cs);
    hs.solve(c, 4);
  }

  public void testIncorrectSolution1() throws Exception{
    Expression e = HampiConstraints.concatExpr(HampiConstraints.varExpr("v0"), HampiConstraints.constExpr("c"));
    Regexp re = HampiConstraints.constRegexp("ca");
    Constraint c = HampiConstraints.regexpConstraint(e, true, re);
    Hampi sol = new Hampi();
    Solution solve = sol.solve(c, 1);
    assertTrue(!solve.isSatisfiable());
  }

  public void testIncorrectSolution3() throws Exception{
    Constraint c = HampiConstraints.andConstraint(HampiConstraints.regexpConstraint(HampiConstraints.concatExpr(HampiConstraints.constExpr("aa"), HampiConstraints.varExpr("v0"), HampiConstraints
        .constExpr("bb")), false, HampiConstraints.starRegexp(HampiConstraints.orRegexp(HampiConstraints.orRegexp(HampiConstraints.concatRegexp(HampiConstraints.concatRegexp(HampiConstraints
        .constRegexp("ba"), HampiConstraints.constRegexp("bb")), HampiConstraints.starRegexp(HampiConstraints.constRegexp("aa"))), HampiConstraints.concatRegexp(HampiConstraints.constRegexp("ba"),
        HampiConstraints.concatRegexp(HampiConstraints.constRegexp("bb"), HampiConstraints.constRegexp("ab")))), HampiConstraints.orRegexp(HampiConstraints.starRegexp(HampiConstraints
        .constRegexp("ba")), HampiConstraints.concatRegexp(HampiConstraints.starRegexp(HampiConstraints.constRegexp("aa")), HampiConstraints.constRegexp("bb")))))), HampiConstraints.regexpConstraint(
        HampiConstraints.varExpr("v0"), false, HampiConstraints.orRegexp(HampiConstraints.starRegexp(HampiConstraints.concatRegexp(HampiConstraints.orRegexp(HampiConstraints.concatRegexp(
            HampiConstraints.constRegexp("ba"), HampiConstraints.constRegexp("bb")), HampiConstraints.starRegexp(HampiConstraints.constRegexp("bb"))), HampiConstraints.concatRegexp(HampiConstraints
            .constRegexp("aa"), HampiConstraints.constRegexp("ba")))), HampiConstraints.constRegexp("ba"))), HampiConstraints.regexpConstraint(HampiConstraints.varExpr("v0"), true, HampiConstraints
        .orRegexp(HampiConstraints.orRegexp(HampiConstraints.starRegexp(HampiConstraints.orRegexp(HampiConstraints.constRegexp("ba"), HampiConstraints.constRegexp("bb"))), HampiConstraints.orRegexp(
            HampiConstraints.orRegexp(HampiConstraints.orRegexp(HampiConstraints.constRegexp("ba"), HampiConstraints.constRegexp("bb")), HampiConstraints.concatRegexp(HampiConstraints
                .constRegexp("bb"), HampiConstraints.constRegexp("ba"))), HampiConstraints.constRegexp("ab"))), HampiConstraints.starRegexp(HampiConstraints.concatRegexp(HampiConstraints
            .starRegexp(HampiConstraints.orRegexp(HampiConstraints.constRegexp("aa"), HampiConstraints.constRegexp("ab"))), HampiConstraints.starRegexp(HampiConstraints.orRegexp(HampiConstraints
            .constRegexp("ab"), HampiConstraints.constRegexp("ba"))))))), HampiConstraints.regexpConstraint(HampiConstraints.varExpr("v0"), true, HampiConstraints.orRegexp(HampiConstraints
        .starRegexp(HampiConstraints.constRegexp("ba")), HampiConstraints.orRegexp(HampiConstraints.starRegexp(HampiConstraints.constRegexp("bb")), HampiConstraints.orRegexp(HampiConstraints
        .concatRegexp(HampiConstraints.constRegexp("bb"), HampiConstraints.starRegexp(HampiConstraints.constRegexp("ba"))), HampiConstraints.orRegexp(HampiConstraints.concatRegexp(HampiConstraints
        .constRegexp("ab"), HampiConstraints.constRegexp("bb")), HampiConstraints.constRegexp("aa")))))), HampiConstraints.regexpConstraint(HampiConstraints.varExpr("v0"), true, HampiConstraints
        .orRegexp(HampiConstraints.starRegexp(HampiConstraints.concatRegexp(HampiConstraints.concatRegexp(HampiConstraints.constRegexp("ba"), HampiConstraints.constRegexp("ba")), HampiConstraints
            .concatRegexp(HampiConstraints.constRegexp("ba"), HampiConstraints.concatRegexp(HampiConstraints.constRegexp("aa"), HampiConstraints.constRegexp("ab"))))), HampiConstraints
            .starRegexp(HampiConstraints.constRegexp("aa")))));
    Hampi sol = new Hampi();
    sol.solve(c, 10);
  }

  public void testIncorrectSolution4() throws Exception{
    Constraint c = HampiConstraints.andConstraint(HampiConstraints.regexpConstraint(HampiConstraints.concatExpr(HampiConstraints.constExpr("bb"), HampiConstraints.varExpr("v0"), HampiConstraints
        .constExpr("aa"), HampiConstraints.varExpr("v0"), HampiConstraints.constExpr("aa")), true, HampiConstraints.starRegexp(HampiConstraints.concatRegexp(HampiConstraints.orRegexp(HampiConstraints
        .orRegexp(HampiConstraints.orRegexp(HampiConstraints.constRegexp("aa"), HampiConstraints.constRegexp("bb")), HampiConstraints.starRegexp(HampiConstraints.constRegexp("aa"))), HampiConstraints
        .constRegexp("ba")), HampiConstraints.concatRegexp(HampiConstraints.starRegexp(HampiConstraints.constRegexp("ab")), HampiConstraints.concatRegexp(HampiConstraints.concatRegexp(
        HampiConstraints.constRegexp("aa"), HampiConstraints.constRegexp("ba")), HampiConstraints.constRegexp("ab")))))), HampiConstraints.regexpConstraint(HampiConstraints.varExpr("v0"), true,
        HampiConstraints.concatRegexp(HampiConstraints.concatRegexp(HampiConstraints.orRegexp(HampiConstraints.constRegexp("aa"), HampiConstraints.starRegexp(HampiConstraints.constRegexp("bb"))),
            HampiConstraints.concatRegexp(HampiConstraints.orRegexp(HampiConstraints.orRegexp(HampiConstraints.constRegexp("aa"), HampiConstraints.constRegexp("ab")), HampiConstraints.orRegexp(
                HampiConstraints.constRegexp("ab"), HampiConstraints.constRegexp("aa"))), HampiConstraints.starRegexp(HampiConstraints.constRegexp("ab")))), HampiConstraints
            .starRegexp(HampiConstraints.concatRegexp(HampiConstraints.constRegexp("ba"), HampiConstraints.concatRegexp(HampiConstraints.starRegexp(HampiConstraints.constRegexp("ab")),
                HampiConstraints.concatRegexp(HampiConstraints.constRegexp("ba"), HampiConstraints.constRegexp("bb"))))))));
    Hampi sol = new Hampi();
    sol.solve(c, 10);
  }

  //VAR(v1) . k . VAR(v1) in [[a-z]* . a . [a-z]* ]
  public void testBugWithRepeatedVar(){
    Regexp a = HampiConstraints.constRegexp("a");
    Regexp[] atozarray = ConstRegexp.createRange('a', 'b');
    Regexp atoz = HampiConstraints.orRegexp(atozarray);
    Regexp atozstar = HampiConstraints.starRegexp(atoz);
    Regexp re = HampiConstraints.concatRegexp(atozstar, a, atozstar); // (at least 1 a)

    Expression v1 = HampiConstraints.varExpr("v1");
    Expression s2 = HampiConstraints.constExpr("b");
    Expression e = HampiConstraints.concatExpr(v1, s2, v1);
    Constraint c = HampiConstraints.regexpConstraint(e, true, re);
    System.out.println(c);
    Solution solution = new Hampi().solve(c, 2);
    System.out.println(solution);
    assertTrue(solution.isSatisfiable());
    assertEquals("ba", solution.getValue(v1));
  }

  public void testRangeBug() throws Exception{
    //VAR(age) in [0]*
    //VAR(age) in 0000

    Regexp[] digitArray = { HampiConstraints.constRegexp("0") };
    Regexp digit = HampiConstraints.orRegexp(digitArray);
    Regexp zeroStar = HampiConstraints.starRegexp(digit);
    Regexp zero4 = HampiConstraints.constRegexp("0000");
    Expression ve = HampiConstraints.varExpr("v1");
    Constraint c1 = HampiConstraints.regexpConstraint(ve, true, zeroStar);
    Constraint c2 = HampiConstraints.regexpConstraint(ve, true, zero4);
    Constraint c = HampiConstraints.andConstraint(c1, c2);
    //    System.out.println(c);
    Solution solution = new Hampi().solve(c, 4);
    assertTrue(solution.isSatisfiable());
    assertEquals("0000", solution.getValue(ve));

  }
}
