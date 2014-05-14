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
import hampi.grammars.Grammar;
import hampi.grammars.apps.GrammarStringBounder;
import hampi.grammars.parser.Parser;
import hampi.stp.STPSolver;
import hampi.tests.gramgren.GrammarTests;
import hampi.utils.*;

import java.util.*;

import junit.framework.TestCase;

public class SolverTests extends TestCase{

  public static void main(String[] args) throws Exception{
    new SolverTests().testGrammarBound2();
  }

  public void testSpeedIntersection() throws Exception{
    for (int i = 1; i <= 15; i++){
      System.out.println("i = " + i);
      intersection(stp(), i);
      System.out.println("---------------------------------------------");
    }
  }

  private void intersection(AbstractSolver solver, int i){
    StopWatch timer = new StopWatch(solver.getName() + " " + i);
    timer.start();
    Hampi hs = new Hampi();
    hs.setSolver(solver);
    Expression v = hs.varExpr("v");
    char[] chars = ASCIITable.range('a', 'z');
    Constraint[] cs = new Constraint[i + 1];
    for (int j = 0; j < cs.length; j++){
      Regexp sigma = hs.rangeRegexp(chars[0], chars[i]);
      Regexp sigmastar = hs.starRegexp(sigma);
      Regexp letter = hs.constRegexp(String.valueOf(chars[j]));
      cs[j] = hs.regexpConstraint(v, true, hs.concatRegexp(sigmastar, letter, sigmastar));
    }
    Constraint c = hs.andConstraint(cs);
    //        System.out.println(c);
    Solution solve = hs.solve(c, i + 1);
    assertTrue(c.toString(), solve.isSatisfiable());
    assertEquals(solve.getValue(v), i + 1, solve.getValue(v).length());
    //    System.out.println(solve.getValue(v));
    timer.stop();
    System.out.println(timer);
    //      System.out.println("---------------------------------------------------");
  }

  public void testSpeed1() throws Exception{
    Hampi hs = new Hampi();
    Regexp white = hs.constRegexp("a");
    Regexp ws = hs.starRegexp(white);
    Regexp f = hs.constRegexp("f");
    Regexp scriptStr = hs.concatRegexp(ws, f, ws, f, ws, f, ws, f, ws, f, ws, f, ws);
    Expression v1 = hs.varExpr("v1");
    Constraint mainConst = hs.regexpConstraint(v1, true, scriptStr);

    Constraint c = hs.andConstraint(mainConst);
    System.out.println(c);
    for (Solution sol : solve(hs, c, 6)){
      System.out.println(sol);

      assertTrue(sol.isSatisfiable());
      assertEquals("ffffff", sol.getValue(v1));
    }
  }

  private AbstractSolver[] all(){
    return new AbstractSolver[] { stp() };
  }

  private STPSolver stp(){
    return new STPSolver();
  }

  private Solution[] solve(Hampi hs, Constraint c, int size, AbstractSolver... solvers){
    if (solvers.length == 0){
      solvers = all();
    }
    Solution[] sols = new Solution[solvers.length];
    for (int i = 0; i < solvers.length; i++){
      hs.setSolver(solvers[i]);
      StopWatch sw = new StopWatch(solvers[i].getName());
      sw.start();
      Solution sol = hs.solve(c, size);
      sw.stop();
      System.out.println(sw);
      sols[i] = sol;
    }
    return sols;
  }

  public void testLameXSS0() throws Exception{
    Hampi h = new Hampi();
    Regexp any = h.starRegexp(h.rangeRegexp('a', 'z'));
    Regexp white = h.constRegexp(" ");
    Regexp ws = h.starRegexp(white);
    Regexp script = h.constRegexp("script");
    Regexp scriptStr = h.concatRegexp(any, h.constRegexp("<"), ws, script, ws, h.constRegexp(">"), any);
    Regexp xssAttack = scriptStr;
    Expression v1 = h.varExpr("v1");
    Constraint mainConst = h.regexpConstraint(v1, true, xssAttack);

    Constraint c = h.andConstraint(mainConst);
    System.out.println(c);
    for (Solution sol : solve(h, c, 8)){
      System.out.println(sol);

      assertTrue(sol.isSatisfiable());
      assertEquals("<script>", sol.getValue(v1));
    }
  }

  public void testLameXSS() throws Exception{
    Hampi h = new Hampi();
    Regexp any = h.starRegexp(h.rangeRegexp(' ', '~'));
    Regexp white = h.constRegexp(" ");
    Regexp ws = h.starRegexp(white);
    Regexp rbr = h.constRegexp(">");
    Regexp lbr = h.constRegexp("<");
    Regexp script = h.constRegexp("script");
    Regexp scriptStr = h.concatRegexp(lbr, ws, script, ws, rbr, ws, h.constRegexp("alert(1);"), ws, lbr, h.constRegexp("/"), script, rbr, ws);
    Regexp xssAttack = h.concatRegexp(any, scriptStr, any);
    Expression v1 = h.varExpr("v1");
    Expression e = h.concatExpr(h.constExpr("Hi "), v1, h.constExpr("!"));
    Constraint mainConst = h.regexpConstraint(e, true, xssAttack);

    Constraint c1 = h.regexpConstraint(v1, false, h.concatRegexp(any, h.constRegexp("<script>"), any));
    Constraint c = h.andConstraint(mainConst, c1);
    System.out.println(c);
    for (Solution sol : solve(h, c, 27, stp())){
      assertTrue(sol.isSatisfiable());
      assertTrue("< script>alert(1);</script>".equals(sol.getValue(v1)) || "<script >alert(1);</script>".equals(sol.getValue(v1)));
    }
  }

  public void testSolutionChecker(){
    Hampi h = new Hampi();
    Regexp aplusb = h.orRegexp(h.constRegexp("a"), h.constRegexp("b"));
    Regexp cplusd = h.orRegexp(h.constRegexp("c"), h.constRegexp("d"));
    Regexp re = h.concatRegexp(aplusb, cplusd); // (a+b)(c+d)
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);

    Solution s = Solution.createSAT();
    s.setValue((VariableExpression) ve, "bd");
    assertTrue(new SolutionChecker().checkSolution(c1, s));
  }

  public void testOneChar() throws Exception{
    Hampi h = new Hampi();
    Regexp re = h.constRegexp("c"); // c
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = h.andConstraint(c1);
    System.out.println(c);
    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("c", solution.getValue(ve));
    }
  }

  public void testTwoChars() throws Exception{
    Hampi h = new Hampi();
    Regexp re = h.constRegexp("ab"); // ab
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = h.andConstraint(c1);
    System.out.println(c);
    for (Solution solution : solve(h, c, 2)){
      assertTrue(solution.isSatisfiable());
      assertEquals("ab", solution.getValue(ve));
    }
  }

  public void testAorB() throws Exception{
    Hampi h = new Hampi();
    Regexp re = h.orRegexp(h.constRegexp("a"), h.constRegexp("b"));//a+b
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = h.andConstraint(c1);
    System.out.println(c);

    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertTrue(Arrays.asList("b", "a").contains(solution.getValue(ve)));
    }
  }

  public void testFriendOrFoe() throws Exception{
    Hampi h = new Hampi();
    Regexp re = h.orRegexp(h.constRegexp("friend"), h.constRegexp("foe"));//friend+foe
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = h.andConstraint(c1);
    System.out.println(c);
    for (Solution solution : solve(h, c, 3)){
      assertTrue(solution.isSatisfiable());
      assertTrue(Arrays.asList("friend", "foe").contains(solution.getValue(ve)));
    }
  }

  public void test1() throws Exception{
    Hampi h = new Hampi();
    Regexp aplusb = h.orRegexp(h.constRegexp("a"), h.constRegexp("b"));
    Regexp aplusbstar = h.starRegexp(aplusb);
    Regexp re = h.concatRegexp(aplusbstar, h.constRegexp("c")); // (a+b)*c
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = h.andConstraint(c1);
    System.out.println(c);
    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("c", solution.getValue(ve));
    }
  }

  public void testAorBCOrD() throws Exception{
    Hampi h = new Hampi();
    Regexp aplusb = h.orRegexp(h.constRegexp("a"), h.constRegexp("b"));
    Regexp cplusd = h.orRegexp(h.constRegexp("c"), h.constRegexp("d"));
    Regexp re = h.concatRegexp(aplusb, cplusd); // (a+b)(c+d)
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = c1;
    for (Solution solution : solve(h, c, 2)){
      assertTrue(solution.isSatisfiable());
      assertTrue(solution.getValue(ve), Arrays.asList("bc", "ac", "ad", "bd").contains(solution.getValue(ve)));
    }
  }

  public void testConcatOfOrs() throws Exception{
    Hampi h = new Hampi();
    Regexp aplusb = h.orRegexp(h.constRegexp("pro"), h.constRegexp("anti"));
    Regexp cplusd = h.orRegexp(h.constRegexp("fred"), h.constRegexp("foo"));
    Regexp re = h.concatRegexp(aplusb, cplusd); // (pro+anti)(fred+foo)
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = c1;
    for (Solution solution : solve(h, c, 8)){
      assertTrue(solution.isSatisfiable());
      assertTrue(solution.getValue(ve), Arrays.asList("profoo", "profred", "antifoo", "antifred").contains(solution.getValue(ve)));
    }
  }

  public void testAStarB() throws Exception{
    Hampi h = new Hampi();
    Regexp astarb = h.concatRegexp(h.starRegexp(h.constRegexp("a")), h.constRegexp("b"));
    Regexp re = astarb;
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = c1;
    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertTrue(solution.getValue(ve), Arrays.asList("b").contains(solution.getValue(ve)));
    }
  }

  public void testDuplicateRegex() throws Exception{
    Hampi h = new Hampi();
    Regexp aastar = h.starRegexp(h.constRegexp("aa"));
    Regexp bb = h.constRegexp("bb");
    Regexp re = h.concatRegexp(aastar, bb, aastar, bb, aastar); // (aa)* bb (aa)* bb (aa)* (exactly 4 bs, in 2 pairs)

    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = h.andConstraint(c1);

    for (Solution solution : solve(h, c, 4)){
      assertTrue(solution.isSatisfiable());
      assertEquals("bbbb", solution.getValue(ve));
    }
  }

  public void test2() throws Exception{
    Hampi h = new Hampi();
    Regexp re = h.constRegexp("ab");

    Expression s1 = h.constExpr("a");
    Expression ve = h.varExpr("v1");
    Expression e = h.concatExpr(s1, ve);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1); // a v1 in ab

    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("b", solution.getValue(ve));
    }
  }

  public void test2a() throws Exception{
    Hampi h = new Hampi();
    Regexp re = h.constRegexp("foobar");

    Expression s1 = h.constExpr("foo");
    Expression ve = h.varExpr("v1");
    Expression e = h.concatExpr(s1, ve);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1); // foo v1 in foobar

    for (Solution solution : solve(h, c, 3)){
      assertTrue(solution.isSatisfiable());
      assertEquals("bar", solution.getValue(ve));
    }
  }

  public void test2b() throws Exception{
    Hampi h = new Hampi();
    Regexp re = h.constRegexp("foobarbaz");

    Expression s1 = h.constExpr("foo");
    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("baz");
    Expression e = h.concatExpr(s1, ve, s2);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1); // foo v1 baz in foobabar

    for (Solution solution : solve(h, c, 3)){
      assertTrue(solution.isSatisfiable());
      assertEquals("bar", solution.getValue(ve));
    }
  }

  public void test2b1() throws Exception{
    Hampi h = new Hampi();
    Regexp re = h.constRegexp("abc");

    Expression s1 = h.constExpr("a");
    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("c");
    Expression e = h.concatExpr(s1, ve, s2);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1); // a v1 c in abc

    h.setSolver(stp());
    Solution solution = h.solve(c, 1);

    assertEquals("b", solution.getValue(ve));
  }

  public void test2c() throws Exception{
    Hampi h = new Hampi();
    Regexp astar = h.starRegexp(h.constRegexp("a"));
    Regexp b = h.constRegexp("b");
    Regexp re = h.concatRegexp(astar, b); // a* b

    Expression s1 = h.constExpr("a");
    Expression ve = h.varExpr("v1");
    Expression e = h.concatExpr(s1, ve);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1); //CONST(a) . VAR(v1) in [a* . b]
    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("b", solution.getValue(ve));
    }
  }

  public void test2d() throws Exception{
    Hampi h = new Hampi();
    Regexp astar = h.starRegexp(h.constRegexp("a"));
    Regexp bb = h.constRegexp("bb");
    Regexp re = h.concatRegexp(astar, bb, astar, bb, astar); // a* bb a* bb a*

    Expression s1 = h.constExpr("a");
    Expression ve = h.varExpr("v1");
    Expression e = h.concatExpr(s1, ve, s1);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1); // a VAR(v1) a in [a* bb a* bb a*]
    for (Solution solution : solve(h, c, 4)){
      assertTrue(solution.isSatisfiable());
      assertEquals("bbbb", solution.getValue(ve));
    }
  }

  public void test2e() throws Exception{
    Hampi h = new Hampi();
    Regexp astar = h.starRegexp(h.constRegexp("a"));
    Regexp b = h.constRegexp("b");
    Regexp re = h.concatRegexp(astar, b, astar, b, astar); // a* b a* b a* (exactly 2 bs)

    Expression s1 = h.constExpr("aabaa");
    Expression ve = h.varExpr("v1");
    Expression e = h.concatExpr(s1, ve);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1); //aabaa v1 in a* b a* b a*
    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("b", solution.getValue(ve));
    }
  }

  public void test3() throws Exception{
    Hampi h = new Hampi();
    Regexp astar = h.starRegexp(h.constRegexp("a"));
    Regexp b = h.constRegexp("b");
    Regexp re = h.concatRegexp(astar, b, astar, b, astar); // a* b a* b a* (exactly 2 bs)

    Expression s1 = h.constExpr("aaabaaa");
    Expression ve = h.varExpr("v1");
    Expression e = h.concatExpr(s1, ve);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1); //aaabaaa v1 in a* b a* b a*
    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("b", solution.getValue(ve));
    }
  }

  public void test4() throws Exception{
    Hampi h = new Hampi();
    Regexp astar = h.starRegexp(h.constRegexp("a"));
    Regexp b = h.constRegexp("b");
    Regexp re = h.concatRegexp(astar, b, astar, b, astar); // a* b a* b a* (exactly 2 bs)

    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("aaa");
    Expression e = h.concatExpr(ve, s2);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1);
    for (Solution solution : solve(h, c, 2)){
      assertTrue(solution.isSatisfiable());
      assertEquals("bb", solution.getValue(ve));
    }
  }

  public void test5() throws Exception{
    Hampi h = new Hampi();
    Regexp astar = h.starRegexp(h.constRegexp("a"));
    Regexp b = h.constRegexp("b");
    Regexp re = h.concatRegexp(astar, b, astar, b, astar); // a* b a* b a* (exactly 2 bs)

    Expression s1 = h.constExpr("b");
    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("a");
    Expression e = h.concatExpr(s1, ve, s2);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1);

    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("b", solution.getValue(ve));
    }
  }

  public void test6() throws Exception{
    Hampi h = new Hampi();
    Regexp astar = h.starRegexp(h.constRegexp("a"));
    Regexp b = h.constRegexp("b");
    Regexp re = h.concatRegexp(astar, b, astar, b, astar); // a* b a* b a* (exactly 2 bs)

    Expression s1 = h.constExpr("ba");
    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("aa");
    Expression e = h.concatExpr(s1, ve, s2);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1);

    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("b", solution.getValue(ve));
      assertEquals("babaa", solution.getValue(e));
    }
  }

  public void test7() throws Exception{
    Hampi h = new Hampi();
    Regexp astar = h.starRegexp(h.constRegexp("a"));
    Regexp b = h.constRegexp("b");
    Regexp re = h.concatRegexp(astar, b, astar, b, astar); // a* b a* b a* (exactly 2 bs)

    Expression s1 = h.constExpr("ba");
    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("ab");
    Expression e = h.concatExpr(s1, ve, s2);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1);

    for (Solution solution : solve(h, c, 0)){
      assertTrue(solution.isSatisfiable());
      assertEquals("", solution.getValue(ve));
    }
  }

  public void test8() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("a");
    Regexp b = h.constRegexp("b");
    Regexp aplusb = h.orRegexp(a, b);
    Regexp aplusbstar = h.starRegexp(aplusb);
    Regexp abba = h.constRegexp("abba");
    Regexp re = h.concatRegexp(aplusbstar, abba, aplusbstar); // (a+b)* abba (a+b)*

    Expression s1 = h.constExpr("babaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaaaaaaaaaaaaaaaa");
    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("aaaaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaaaaaaaaaaaaaaaabbbbb");
    Expression e = h.concatExpr(s1, ve, s2);
    Constraint c = h.regexpConstraint(e, true, re);

    System.out.println(c);
    for (Solution solution : solve(h, c, 2)){
      assertTrue(solution.isSatisfiable());
      assertEquals("bb", solution.getValue(ve));
    }
  }

  // a + var + a = "" (no solutions trivially)
  public void test9() throws Exception{
    Hampi h = new Hampi();
    Expression s1 = h.constExpr("a");
    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("a");
    Expression e = h.concatExpr(s1, ve, s2);
    Regexp re = h.constRegexp(""); // empty string
    Constraint c = h.regexpConstraint(e, true, re);

    for (Solution solution : solve(h, c, 1)){
      assertTrue(!solution.isSatisfiable());
    }
  }

  public void testSigmaStarASigmaStar() throws Exception{
    Hampi h = new Hampi();

    Regexp sigma = h.rangeRegexp('a', 'z');
    Regexp sigmaStar = h.starRegexp(sigma);
    Expression ve = h.varExpr("v1");

    Regexp re1 = h.concatRegexp(sigmaStar, h.constRegexp("a"), sigmaStar);

    Constraint c1 = h.regexpConstraint(ve, true, re1);

    Constraint c = h.andConstraint(c1);
    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      String value = solution.getValue(ve);
      assertEquals("a", value);
    }
  }

  public void testTwiceSigmaStarLetterSigmaStar() throws Exception{
    Hampi h = new Hampi();

    Regexp sigma = h.rangeRegexp('a', 'z');
    Regexp sigmaStar = h.starRegexp(sigma);

    Expression ve = h.varExpr("v1");

    Regexp re1 = h.concatRegexp(sigmaStar, h.constRegexp("a"), sigmaStar);
    Regexp re2 = h.concatRegexp(sigmaStar, h.constRegexp("b"), sigmaStar);

    Constraint c1 = h.regexpConstraint(ve, true, re1);
    Constraint c2 = h.regexpConstraint(ve, true, re2);

    Constraint c = h.andConstraint(c1, c2);
    for (Solution solution : solve(h, c, 2)){
      assertTrue(solution.isSatisfiable());
      assertTrue(solution.getValue(ve), Arrays.asList("ab", "ba").contains(solution.getValue(ve)));
    }
  }

  public void testEmptyStringSatisfies() throws Exception{
    Hampi h = new Hampi();
    Expression e = h.varExpr("v1");
    Regexp re = h.starRegexp(h.constRegexp("a")); // a*
    Constraint c1 = h.regexpConstraint(e, true, re);
    System.out.println(c1);
    for (Solution solution : solve(h, c1, 0)){
      assertTrue(solution.isSatisfiable());
      assertTrue(solution.isValidFor(c1));
    }
  }

  public void testNotMembership0() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("a");
    Regexp b = h.constRegexp("b");

    Regexp aorb = h.orRegexp(a, b);

    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, false, b);
    Constraint c2 = h.regexpConstraint(ve, true, aorb);
    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("a", solution.getValue(ve));
    }
  }

  public void testNotMembership1() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("a");
    Regexp b = h.constRegexp("b");
    Regexp ab = h.constRegexp("ab");

    Regexp aorb = h.orRegexp(a, b);

    Expression v = h.varExpr("v");
    Expression av = h.concatExpr(h.constExpr("a"), v);
    Constraint c1 = h.regexpConstraint(av, false, ab);
    Constraint c2 = h.regexpConstraint(v, true, aorb);
    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 1, stp())){
      assertTrue(solution.isSatisfiable());
      assertEquals("a", solution.getValue(v));
    }
  }

  public void testNotMembership() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("a");
    Regexp astar = h.starRegexp(a);
    Regexp b = h.constRegexp("b");
    Regexp re = h.orRegexp(astar, h.concatRegexp(astar, b, astar)); // a* + a* b a*  (zero or one b)

    Regexp sigmastar = h.starRegexp(h.orRegexp(a, b));

    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, false, re);
    Constraint c2 = h.regexpConstraint(ve, true, sigmastar);
    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 2)){
      assertTrue(solution.isSatisfiable());
      assertEquals("bb", solution.getValue(ve));
    }
  }

  public void testUnsat1() throws Exception{
    Hampi h = new Hampi();
    Regexp astar = h.starRegexp(h.constRegexp("a"));
    Regexp b = h.constRegexp("b");
    Regexp re = h.concatRegexp(astar, b, astar, b, astar); // a* b a* b a* (exactly 2 bs)

    Expression s1 = h.constExpr("b");
    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("abab");
    Expression e = h.concatExpr(s1, ve, s2);
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint c = h.andConstraint(c1);

    for (Solution solution : solve(h, c, 1)){
      assertTrue(!solution.isSatisfiable());
    }
  }

  public void testOverlap() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("a");
    Regexp astar = h.starRegexp(a);
    Regexp re = h.concatRegexp(a, astar, a); // a a* a

    Expression v1 = h.varExpr("v1");
    Expression e = v1;//v1
    Constraint c1 = h.regexpConstraint(e, true, re);
    Constraint constr = c1;

    for (Solution solution : solve(h, constr, 2)){
      assertTrue(solution.isSatisfiable());
      assertEquals("aa", solution.getValue(v1));//both a's are required
    }
  }

  public void testRange1() throws Exception{
    Hampi h = new Hampi();
    Regexp re = h.rangeRegexp('a', 'z');

    Expression v1 = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(v1, true, re);
    Constraint constr = c1;
    System.out.println(constr);

    for (Solution solution : solve(h, constr, 1)){
      assertTrue(solution.isSatisfiable());
      String v = solution.getValue(v1);
      assertEquals(1, v.length());
      assertTrue(re.getUsedCharacters().contains(v.charAt(0)));
    }
  }

  public void testOverlap1() throws Exception{
    Hampi h = new Hampi();
    Regexp fred = h.constRegexp("fred");
    Regexp dulce = h.constRegexp("dulce");
    Regexp[] atozarray = ConstRegexp.createRange('a', 'z');
    Regexp atoz = h.orRegexp(atozarray);
    Regexp atozstar = h.starRegexp(atoz);
    Regexp re = h.concatRegexp(fred, atozstar, dulce); // fred [a-z]* dulce

    Expression v1 = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(v1, true, re);
    Constraint constr = h.andConstraint(c1);

    for (Solution solution : solve(h, constr, 9)){
      assertTrue(solution.isSatisfiable());
      assertEquals("freddulce", solution.getValue(v1));//both d's are required
    }
  }

  public void testOverlap2() throws Exception{
    Hampi h = new Hampi();
    Regexp fd = h.constRegexp("fd");
    Regexp d = h.constRegexp("d");
    Regexp[] atozarray = ConstRegexp.createRange('a', 'z');
    Regexp atoz = h.orRegexp(atozarray);
    Regexp atozstar = h.starRegexp(atoz);
    Regexp re = h.concatRegexp(fd, atozstar, d); // fd [a-z]* d

    Expression v1 = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(v1, true, re);
    Constraint constr = h.andConstraint(c1);

    for (Solution solution : solve(h, constr, 3)){
      assertTrue(solution.isSatisfiable());
      assertEquals("fdd", solution.getValue(v1));//both d's are required
    }
  }

  public void test11() throws Exception{
    Hampi h = new Hampi();
    Regexp foo = h.constRegexp("foo");
    Regexp barnaba = h.constRegexp("barnabaaaaaaa");
    Regexp[] atozarray = ConstRegexp.createRange('a', 'z');
    Regexp atoz = h.orRegexp(atozarray);
    Regexp atozstar = h.starRegexp(atoz);
    Regexp re = h.concatRegexp(foo, atozstar, barnaba); // foo [a-z]* bar

    Expression v1 = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(v1, true, re);
    Constraint constr = h.andConstraint(c1);

    for (Solution solution : solve(h, constr, 16)){
      assertTrue(solution.isSatisfiable());
      assertEquals("foobarnabaaaaaaa", solution.getValue(v1));
    }
  }

  //this fails if lengths are calculated badly
  public void test12() throws Exception{
    Hampi h = new Hampi();
    Regexp b = h.constRegexp("b");
    Regexp ab = h.constRegexp("ab");

    Expression v = h.varExpr("v");
    Expression av = h.concatExpr(h.constExpr("a"), v);
    Constraint c1 = h.regexpConstraint(v, true, b); //v in b
    Constraint c2 = h.regexpConstraint(av, true, ab); //a v in a b

    Constraint constr = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, constr, 1, stp())){
      assertTrue(solution.isSatisfiable());
      assertEquals("b", solution.getValue(v));
    }

  }


  public void testMultiConstraints() throws Exception{
    Hampi h = new Hampi();
    Regexp s1 = h.constRegexp("tiger");
    Regexp s2 = h.constRegexp("rwanda");
    Regexp[] atozarray = ConstRegexp.createRange('a', 'z');
    Regexp atoz = h.orRegexp(atozarray);
    Regexp atozstar = h.starRegexp(atoz);
    Regexp re = h.concatRegexp(s1, atozstar, s2); // tiger [a-z]* rwanda

    Regexp whatever = h.constRegexp("error");
    Regexp re2 = h.concatRegexp(atozstar, whatever, atozstar);

    Expression v1 = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(v1, true, re);
    Constraint c2 = h.regexpConstraint(v1, true, re2);
    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 13)){
      assertTrue(solution.isSatisfiable());
      assertEquals("tigerrorwanda", solution.getValue(v1));
    }
  }
/**
 * var v:5;
   val prefix := v[0:2];
   val suffix := v[2:3];
   reg r1 := star("a");
   reg r2 := star("b");
   assert prefix in r1;
   assert suffix in r2;
   //expecting aabbb
 */
  public void testSubsequenceConstraints() throws Exception{
    Hampi h = new Hampi();
    VariableExpression v = h.varExpr("v");
    Expression prefix = h.subsequenceExpr(v, 0, 2);
    Expression suffix = h.subsequenceExpr(v, 2, 3);
    Regexp r1 = h.starRegexp(h.constRegexp('a'));
    Regexp r2 = h.starRegexp(h.constRegexp('b'));

    Constraint c1 = h.regexpConstraint(prefix, true, r1);
    Constraint c2 = h.regexpConstraint(suffix, true, r2);
    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 5)){
      assertTrue(solution.isSatisfiable());
      assertEquals("aabbb", solution.getValue(v));
    }
  }

  /**
   * var v:4;
     val prefix := v[0:2];
     val compose := concat("a",prefix,"b",v,"c");
     assert prefix in "x*";
     assert compose in "axxbxxppc";
     //expecting xxpp
   */
  public void testSubsequenceAndVarInSameConcat() throws Exception{
    Hampi h = new Hampi();
    VariableExpression v = h.varExpr("v");
    Expression prefix = h.subsequenceExpr(v, 0, 2);
    Expression compose = h.concatExpr(h.constExpr("a"), prefix, h.constExpr("b"), v, h.constExpr("c"));
    Regexp r1 = h.starRegexp(h.constRegexp('x'));
    Constraint c1 = h.regexpConstraint(prefix, true, r1);
    Constraint c2 = h.regexpConstraint(compose, true, h.constRegexp("axxbxxppc"));
    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 4)){
      assertTrue(solution.isSatisfiable());
      assertEquals("xxpp", solution.getValue(v));
    }
  }

  /**
   * var v:4;
   * val prefix := v[0:2];
   * assert prefix in "xx";
   * //expecting xx??
   */
  public void testSubsequenceInConstantRegExp() throws Exception{
    Hampi h = new Hampi();
    VariableExpression v = h.varExpr("v");
    Expression prefix = h.subsequenceExpr(v, 0, 2);
    Constraint c = h.regexpConstraint(prefix, true, h.constRegexp("xx"));

    for (Solution solution : solve(h, c, 4)){
      assertTrue(solution.isSatisfiable());
      assertEquals("xx??", solution.getValue(v));
    }
  }
/**
 * var a:6;
val compose := concat("a",a,"b",a);
assert compose contains "aaabaa";
 */
  public void testMultipleOccurencesOFVariableInConcat() throws Exception{
    Hampi h = new Hampi();
    VariableExpression a = h.varExpr("a");
    Expression compose = h.concatExpr(h.constExpr("a"), a, h.constExpr("b"), a);

    Constraint c = h.regexpConstraint(compose, true, h.constRegexp("aaabaa"));

    for (Solution solution : solve(h, c, 2)){
      assertTrue(solution.isSatisfiable());
      assertEquals("aa", solution.getValue(a));
    }
  }
  /**
   * var v:4; val prefix := v[0:2]; val compose := concat("a",prefix,"b",v,"c");
   * assert prefix in "xx"; assert compose in "axxbxxppc"; //expecting xxpp
   */
  public void testSubsequenceAndVarInSameConcat2() throws Exception{
    Hampi h = new Hampi();
    VariableExpression v = h.varExpr("v");
    Expression prefix = h.subsequenceExpr(v, 0, 2);
    Expression compose = h.concatExpr(h.constExpr("a"), prefix, h.constExpr("b"), v, h.constExpr("c"));

    Constraint c1 = h.regexpConstraint(prefix, true, h.constRegexp("xx"));
    Constraint c2 = h.regexpConstraint(compose, true, h.constRegexp("axxbxxppc"));
    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 4)){
      assertTrue(solution.isSatisfiable());
      assertEquals("xxpp", solution.getValue(v));
    }
  }

  /**
   * var v:9;
   * val vSub1 := v[0:3]; //substring of v (offset 2, length 3)
   * val vSub2 := v[3:3];
   * val vSub3 := v[6:3];
   * val vSub4 := v[2:2];
   * val c     := "deg";
   * reg sigmaStar := star(['a'-'z']);
   * reg r         := concat('b',sigmaStar);
   * assert vSub1 contains "de";
   * assert vSub2 contains "ef";
   * assert vSub1 equals c;
   * assert vSub1 not equals vSub4;
   * assert vSub4 not equals c;
   * assert v not equals c;
   * assert vSub3 in r;
   * assert vSub3 equals vSub2;
   */
  public void testEqualsAndNotEquals() throws Exception{
    Hampi h = new Hampi();
    VariableExpression v = h.varExpr("v");
    Expression vSub1 = h.subsequenceExpr(v, 0, 3);
    Expression vSub2 = h.subsequenceExpr(v, 3, 3);
    Expression vSub3 = h.subsequenceExpr(v, 6, 3);
    Expression vSub4 = h.subsequenceExpr(v, 2, 2);
    Expression c = h.constExpr("deg");
    Regexp sigma_star = h.starRegexp(h.rangeRegexp((char) 0, (char) 255));
    Regexp r = h.concatRegexp(h.constRegexp("b"), sigma_star);

    Constraint c1 = h.regexpConstraint(vSub1, true, h.concatRegexp(sigma_star, h.constRegexp("de"), sigma_star));
    Constraint c2 = h.regexpConstraint(vSub2, true, h.concatRegexp(sigma_star, h.constRegexp("ef"), sigma_star));
    Constraint c3 = h.equalsConstraint(vSub1, true, c);
    Constraint c4 = h.equalsConstraint(vSub1, false, vSub4);
    Constraint c5 = h.equalsConstraint(vSub4, false, c);
    Constraint c6 = h.equalsConstraint(v, false, c);
    Constraint c7 = h.regexpConstraint(vSub3, true, r);
    Constraint c8 = h.equalsConstraint(vSub3, true, vSub2);
    Constraint constraint = h.andConstraint(c1, c2, c3, c4, c5, c6, c7, c8);

    for (Solution solution : solve(h, constraint, 9)){
      assertTrue(solution.isSatisfiable());
      assertEquals("degbefbef", solution.getValue(v));
    }
  }

  /**
   * var v:2; assert v in "xx"; //expecting xx
   */
  public void testVarInConstantRegExp() throws Exception{
    Hampi h = new Hampi();
    Expression v = h.varExpr("v");
    Constraint c = h.regexpConstraint(v, true, h.constRegexp("xx"));

    for (Solution solution : solve(h, c, 2)){
      assertTrue(solution.isSatisfiable());
      assertEquals("xx", solution.getValue(v));
    }
  }

  /**
   * var v:6;
   * val vSub := v[2:3]; //substring of v (offset 2, length 3)
   * assert v contains "fred";
   * assert vSub contains "de"
   * //EXPECT v = frede
   */
  public void testSubsequenceAndVarSimpleConcat() throws Exception{
    Hampi h = new Hampi();
    VariableExpression v = h.varExpr("v");
    Expression vSub = h.subsequenceExpr(v, 2, 3);
    Regexp sigma_star = h.starRegexp(h.rangeRegexp((char) 0, (char) 255));
    Constraint c1 = h.regexpConstraint(v, true, h.concatRegexp(sigma_star, h.constRegexp("fred"), sigma_star));
    Constraint c2 = h.regexpConstraint(vSub, true, h.concatRegexp(sigma_star, h.constRegexp("de"), sigma_star));

    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 5)){
      assertTrue(solution.isSatisfiable());
      assertEquals("frede", solution.getValue(v));
    }
  }

  /**
   * var v:4; val vSub := v[2:3]; //substring of v (offset 2, length 3) assert v
   * contains "fred"; assert vSub contains "de"; //EXPECT v = frede
   */
  public void testSubsequenceAndVarSimpleConcatToShortVar() throws Exception{
    Hampi h = new Hampi();
    VariableExpression v = h.varExpr("v");
    Expression vSub = h.subsequenceExpr(v, 2, 3);
    Regexp sigma_star = h.starRegexp(h.rangeRegexp((char) 0, (char) 255));
    Constraint c1 = h.regexpConstraint(v, true, h.concatRegexp(sigma_star, h.constRegexp("fred"), sigma_star));
    Constraint c2 = h.regexpConstraint(vSub, true, h.concatRegexp(sigma_star, h.constRegexp("de"), sigma_star));

    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 4)){
      assertFalse(solution.isSatisfiable());
    }
  }


  public void testMultiConstraints2() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("a");
    Regexp[] atozarray = ConstRegexp.createRange('a', 'z');
    Regexp atoz = h.orRegexp(atozarray);
    Regexp atozstar = h.starRegexp(atoz);
    Regexp re = h.concatRegexp(atozstar, a, atozstar, a, atozstar); // [a-z]* a [a-z]* a [a-z]* (at least 2 a)

    Regexp b = h.constRegexp("b");
    Regexp c = h.constRegexp("c");
    Regexp re2 = h.concatRegexp(atozstar, b, atozstar, c); // [a-z]* b [a-z]* c (at least 1 b and end with c)

    Expression v1 = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(v1, true, re);
    Constraint c2 = h.regexpConstraint(v1, true, re2);
    Constraint constr = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, constr, 4)){
      assertTrue(solution.isSatisfiable());
      solution.isValidFor(constr);
    }
  }

  public void testMultiConstraints3() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("a");
    Regexp[] atozarray = ConstRegexp.createRange('a', 'z');
    Regexp atoz = h.orRegexp(atozarray);
    Regexp atozstar = h.starRegexp(atoz);
    Regexp re = h.concatRegexp(atozstar, a, atozstar, a, atozstar); // [a-z]* a [a-z]* a [a-z]* (at least 2 a)

    Regexp f = h.constRegexp("f");
    Regexp c = h.constRegexp("c");
    Regexp re2 = h.concatRegexp(atozstar, f, atozstar, c); // [a-z]* f [a-z]* c (at least 1 f and end with c)

    Regexp re3 = h.concatRegexp(atozstar, h.constRegexp("fred"), atozstar); // [a-z]* fred [a-z]* (at least fred)

    Expression v1 = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(v1, true, re);
    Constraint c2 = h.regexpConstraint(v1, true, re2);
    Constraint c3 = h.regexpConstraint(v1, true, re3);
    Constraint constr = h.andConstraint(c1, c2, c3);
    //    System.out.println(constr);

    for (Solution solution : solve(h, constr, 10)){
      assertTrue(solution.isSatisfiable());
      solution.isValidFor(constr);
    }
  }

  public void testMultiConstraints4() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("a");
    Regexp[] atozarray = ConstRegexp.createRange('a', 'z');
    Regexp atoz = h.orRegexp(atozarray);
    Regexp atozstar = h.starRegexp(atoz);
    Regexp re = h.concatRegexp(atozstar, a, atozstar, a, atozstar); // [a-z]* a [a-z]* a [a-z]* (at least 2 a)

    Regexp fred = h.constRegexp("fred");
    Regexp c = h.constRegexp("c");
    Regexp re2 = h.concatRegexp(atozstar, fred, atozstar, c); // [a-z]* fred [a-z]* c (at least 1 fred and end with c)

    Expression v1 = h.varExpr("v1");

    Expression s1 = h.constExpr("gosia");
    Expression ve = h.varExpr("v1");
    Expression s2 = h.constExpr("chomik");
    Expression e0 = h.concatExpr(s1, ve, s2);

    Expression e = v1;
    Constraint c1 = h.regexpConstraint(e0, true, re);
    Constraint c2 = h.regexpConstraint(e, true, re2);
    Constraint constr = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, constr, 10)){
      assertTrue(solution.isSatisfiable());
      assertTrue(solution.isValidFor(constr));
    }
  }

  public void testInt() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("3");
    Regexp re = a;

    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, true, re);
    Constraint c = h.andConstraint(c1);

    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("3", solution.getValue(ve));
    }
  }

  public void testIntIneqality() throws Exception{
    Hampi h = new Hampi();
    Regexp a = h.constRegexp("3");
    Regexp re = a;

    Regexp[] digitArray = ConstRegexp.createRange('0', '9');
    Regexp digit = h.orRegexp(digitArray);
    Regexp digitstar = h.starRegexp(digit);
    Regexp number = h.concatRegexp(digit, digitstar);
    Expression ve = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(ve, false, re);
    Constraint c2 = h.regexpConstraint(ve, true, number);

    Constraint c = h.andConstraint(c1, c2);
    System.out.println(c);
    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertTrue(!solution.getValue(ve).equals("3"));
    }
  }

  private Regexp getDigitPlus(){
    Hampi h = new Hampi();
    Regexp[] digitArray = ConstRegexp.createRange('0', '9');
    Regexp digit = h.orRegexp(digitArray);
    Regexp digitstar = h.starRegexp(digit);
    return h.concatRegexp(digit, digitstar);
  }

  public void testNumbers() throws Exception{
    Hampi h = new Hampi();
    Expression ve = h.varExpr("age");
    Constraint c1 = h.regexpConstraint(ve, true, getDigitPlus()); //bug only happens if this is a concat
    Constraint c2 = h.regexpConstraint(ve, true, h.constRegexp("4"));
    Constraint c = h.andConstraint(c1, c2);

    for (Solution solution : solve(h, c, 1)){
      assertTrue(solution.isSatisfiable());
      assertEquals("4", solution.getValue(ve));
    }
  }

  public void testMultiConstraints0() throws Exception{
    //VAR(v1) in [[a-b]* a [a-b]*] //at least 1 a
    //VAR(v1) in [[a-b]* b [a-b]*] //at least 1 b

    Hampi h = new Hampi();
    Regexp any = h.starRegexp(h.rangeRegexp('a', 'b'));
    Regexp a = h.constRegexp("a");
    Regexp b = h.constRegexp("b");
    Regexp someA = h.concatRegexp(any, a, any);
    Regexp someB = h.concatRegexp(any, b, any);
    Expression v1 = h.varExpr("v1");
    Constraint c1 = h.regexpConstraint(v1, true, someA);
    Constraint c2 = h.regexpConstraint(v1, true, someB);

    Constraint c = h.andConstraint(c1, c2);
    for (Solution sol : solve(h, c, 2)){
      assertTrue(sol.isSatisfiable());
      assertTrue(sol.isValidFor(c));
    }
  }

  public void testGrammarBound1() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "test_generate_parent.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "expr", 16, false);

    Hampi h = new Hampi();
    h.setSolver(stp());
    Constraint rc = h.regexpConstraint(h.varExpr("v"), true, boundedRegexp);
    Regexp threeOpens = h.concatRegexp(h.constRegexp("((("), h.starRegexp(h.orRegexp(h.constRegexp("("), h.constRegexp(")"))));
    Constraint rc2 = h.regexpConstraint(h.varExpr("v"), true, threeOpens);
    Constraint c = h.andConstraint(rc, rc2);
    Solution solve = h.solve(c, 16);
    System.out.println(c);
    assertTrue(solve.isSatisfiable());
    assertTrue(solve.isValidFor(c));
    System.out.println(solve);
  }

  public void testGrammarBound2() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "test_arithm.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 24;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "S", bound, false);
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Constraint rc = h.regexpConstraint(h.varExpr("v"), true, boundedRegexp);
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Regexp threeOpens = h.concatRegexp(h.constRegexp("((("), sigmaStar, h.constRegexp(")+b_)"), sigmaStar, h.constRegexp(")-a_)"), sigmaStar);
    Constraint rc2 = h.regexpConstraint(h.varExpr("v"), true, threeOpens);
    Constraint c = h.andConstraint(rc, rc2);
    //    System.out.println(c);
    Solution solve = h.solve(c, 24);
    assertTrue(solve.isSatisfiable());
    assertTrue(solve.isValidFor(c));
    System.out.println(solve);

  }

  public void testGrammarBound3() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "test_arithm.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 11;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "S", bound, false);
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Constraint rc = h.regexpConstraint(h.varExpr("v"), true, boundedRegexp);
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Regexp expr1 = h.concatRegexp(sigmaStar, h.constRegexp("(ab+"), sigmaStar);
    Constraint rc2 = h.regexpConstraint(h.varExpr("v"), true, expr1);
    Regexp expr2 = h.concatRegexp(sigmaStar, h.constRegexp("+ab)"), sigmaStar);
    Constraint rc3 = h.regexpConstraint(h.varExpr("v"), true, expr2);
    Constraint c = h.andConstraint(rc, rc2, rc3);
    //        System.out.println(c);
    Solution solve = h.solve(c, bound);
    assertTrue(solve.isSatisfiable());
    assertTrue(solve.isValidFor(c));
    System.out.println(solve);
  }

  public void testGrammarBound4() throws Exception{
    Grammar g = new Parser(GrammarTests.DIR + "test_arithm.txt").parse();
    GrammarStringBounder gsb = new GrammarStringBounder();
    int bound = 9;
    Regexp boundedRegexp = gsb.getBoundedRegexp(g, "S", bound, false);
    Set<Character> alpha = boundedRegexp.getUsedCharacters();
    Hampi h = new Hampi();
    h.setSolver(stp());
    Constraint rc = h.regexpConstraint(h.varExpr("v"), true, boundedRegexp);
    Regexp sigmaStar = h.starRegexp(h.orRegexp(h.orRegexp(charRegexp(alpha, h))));
    Regexp expr1 = h.concatRegexp(h.constRegexp("(ab+0000"), sigmaStar);
    Constraint rc2 = h.regexpConstraint(h.varExpr("v"), true, expr1);
    Constraint c = h.andConstraint(rc, rc2);
    //        System.out.println(c);
    Solution solve = h.solve(c, bound);
    assertTrue(solve.isSatisfiable());
    assertTrue(solve.isValidFor(c));
    System.out.println(solve);
  }

  public void testRegexp() throws Exception{
    String pattern = "(\\()([a-zA-Z])(\\+|\\-)([a-zA-Z])(\\))";
    boolean matches = "(a+b)".matches(pattern);
    assertTrue(matches);
  }

  private List<Regexp> charRegexp(Set<Character> alpha, Hampi h){
    List<Regexp> result = new ArrayList<Regexp>();
    for (char ch : alpha){
      result.add(h.constRegexp(ch));
    }
    return result;
  }

  public void testNestedRegexp1() throws Exception{
    Hampi h = new Hampi();
    h.setSolver(stp());
    Expression v0 = h.varExpr("v0");
    Regexp a = h.constRegexp("a");
    Regexp b = h.constRegexp("b");
    Constraint c1 = h.regexpConstraint(v0, true, a);
    Regexp leftConcatPart = h.starRegexp(a);
    Regexp rightConcatPart = h.starRegexp(b);
    Regexp leftStar = h.starRegexp(h.concatRegexp(leftConcatPart, rightConcatPart));
    Constraint c2 = h.regexpConstraint(v0, true, leftStar);
    Constraint c = h.andConstraint(c1, c2);
    Solution solve = h.solve(c, 1);
    assertTrue(solve.isSatisfiable());
    assertEquals("a", solve.getValue(v0));
  }

  public void testSolutionValidity() throws Exception{
    Hampi h = new Hampi();
    Expression v = h.varExpr("v0");
    Constraint c = h.andConstraint(h.regexpConstraint(v, true, h.starRegexp(h.concatRegexp(h.constRegexp("bab"), h.starRegexp(h.orRegexp(h.concatRegexp(h.constRegexp("aba"), h.starRegexp(h
        .concatRegexp(h.constRegexp("aab"), h.constRegexp("aaa")))), h.starRegexp(h.orRegexp(h.constRegexp("baa"), h.orRegexp(h.constRegexp("abb"), h.constRegexp("bbb"))))))))), h.regexpConstraint(v,
        true, h.orRegexp(h.constRegexp("bba"), h.concatRegexp(h.starRegexp(h.constRegexp("bbb")), h.starRegexp(h.constRegexp("aba"))))));
    System.out.println(c);
    Solution s = Solution.createSAT();
    s.setValue((VariableExpression) v, "");
    assertTrue(s.isValidFor(c));
  }

  public void testStarDistribution() throws Exception{
    Hampi h = new Hampi();
    Expression v = h.varExpr("v0");
    Constraint c1 = h.regexpConstraint(v, true, h.starRegexp(h.constRegexp("bb")));
    Constraint c2 = h.regexpConstraint(v, true, h.constRegexp("bb"));
    Constraint c = h.andConstraint(c1, c2);
    h.setSolver(new STPSolver());
    Solution solve = h.solve(c, 2);
    System.out.println(solve);

    Solution s = Solution.createSAT();
    s.setValue((VariableExpression) v, "bb");
    assertTrue(s.isValidFor(c));
    assertTrue(solve.isSatisfiable());
  }

  public void testInvalidSolution() throws Exception{
    Hampi h = new Hampi();
    Expression v = h.varExpr("v0");
    Constraint c1 = h.regexpConstraint(v, true, h.starRegexp(h.concatRegexp(h.constRegexp("ba"))));
    Constraint c2 = h.regexpConstraint(v, true, h.orRegexp(h.orRegexp(h.concatRegexp(h.constRegexp("b"), h.concatRegexp(h.starRegexp(h.constRegexp("b")))))));
    Constraint c = h.andConstraint(c1, c2);
    h.setSolver(stp());
    Solution solve = h.solve(c, 10);
    assertTrue(solve.isValidFor(c));
  }

  public void testSlowness2() throws Exception{
    Hampi h = new Hampi();

    Constraint c1 = h.regexpConstraint(h.varExpr("v0"), true, h.concatRegexp(h.concatRegexp(h.starRegexp(h.concatRegexp(h.starRegexp(h.constRegexp("b")))), h.constRegexp("ba"))));
    Constraint c2 = h.regexpConstraint(h.varExpr("v0"), true, h.concatRegexp(h.concatRegexp(h.starRegexp(h.concatRegexp(h.concatRegexp(h.constRegexp("ab")))))));
    Constraint c = h.andConstraint(c1, c2);

    h.setSolver(stp());
    Solution solveStp = h.solve(c, 10);
    System.out.println("stp:" + solveStp);

    assertTrue(!solveStp.isSatisfiable());
  }

  public void DISABLEDtestSlowness3() throws Exception{
    Hampi h = new Hampi();
    Constraint c1 = h.regexpConstraint(h.varExpr("v0"), true, h.concatRegexp(h.concatRegexp(h.concatRegexp(h.constRegexp("aab"), h.orRegexp(h.orRegexp(h.concatRegexp(h.orRegexp(h.constRegexp("abb"),
        h.constRegexp("baa")), h.constRegexp("bab")), h.constRegexp("aab")), h.constRegexp("abb"))), h.constRegexp("bbb")), h.concatRegexp(h.starRegexp(h.constRegexp("aaa")), h.orRegexp(h.orRegexp(h
        .starRegexp(h.orRegexp(h.constRegexp("bab"), h.constRegexp("bab"))), h.constRegexp("aba")), h.starRegexp(h.orRegexp(h.starRegexp(h.constRegexp("baa")), h.orRegexp(h.concatRegexp(h
        .constRegexp("bbb"), h.constRegexp("abb")), h.constRegexp("bba"))))))));
    Constraint c2 = h.regexpConstraint(h.varExpr("v0"), true, h.orRegexp(h.orRegexp(h.starRegexp(h.orRegexp(h.orRegexp(h.constRegexp("aab"), h.orRegexp(h.orRegexp(h.constRegexp("aaa"), h
        .constRegexp("bab")), h.concatRegexp(h.constRegexp("aaa"), h.constRegexp("bba")))), h.constRegexp("aab"))), h.starRegexp(h.concatRegexp(h.orRegexp(h.starRegexp(h.constRegexp("abb")), h
        .concatRegexp(h.constRegexp("baa"), h.constRegexp("aaa"))), h.constRegexp("bbb")))), h.starRegexp(h.orRegexp(h.orRegexp(h.concatRegexp(h.starRegexp(h.orRegexp(h.constRegexp("aaa"), h
        .constRegexp("abb"))), h.starRegexp(h.orRegexp(h.constRegexp("baa"), h.constRegexp("baa")))), h.constRegexp("baa")), h.starRegexp(h.concatRegexp(h.concatRegexp(h.constRegexp("aab"), h
        .orRegexp(h.constRegexp("aaa"), h.constRegexp("bab"))), h.starRegexp(h.orRegexp(h.constRegexp("aaa"), h.constRegexp("baa")))))))));
    Constraint c = h.andConstraint(c1, c2);

    h.setSolver(stp());
    Solution solveStp = h.solve(c, 20);
    System.out.println("stp:" + solveStp);

    assertTrue(!solveStp.isSatisfiable());

  }

  public void testInvalidSolution2() throws Exception{
    Hampi h = new Hampi();
    Expression v = h.varExpr("v0");
    Constraint c1 = h.regexpConstraint(v, true, h.starRegexp(h.orRegexp(h.constRegexp("a"), h.constRegexp("ab"))));
    Constraint c2 = h.regexpConstraint(v, true, h.constRegexp("ab"));
    Constraint c = h.andConstraint(c1, c2);
    h.setSolver(stp());
    Solution stpsolve = h.solve(c, 2);

    assertEquals("ab", stpsolve.getValue(v));
  }

  public void testInvalidSolution3() throws Exception{
    Hampi h = new Hampi();
    Expression v = h.varExpr("v0");
    Constraint c1 = h.regexpConstraint(v, true, h.constRegexp("b"));
    Constraint c2 = h.regexpConstraint(v, true, h.starRegexp(h.orRegexp(h.constRegexp("a"), h.starRegexp(h.constRegexp("a")))));
    Constraint c = h.andConstraint(c1, c2);
    h.setSolver(stp());
    Solution solve = h.solve(c, 1);
    assertTrue(!solve.isSatisfiable());
    assertTrue(solve.isValidFor(c));
  }

  public void testMissingSolution() throws Exception{
    Hampi h = new Hampi();
    Constraint c1 = h.regexpConstraint(h.varExpr("v0"), true, h.concatRegexp(h.constRegexp("baa"), h.concatRegexp(h.concatRegexp(h.concatRegexp(h.concatRegexp(h.constRegexp("aab"), h
        .constRegexp("aba")), h.orRegexp(h.concatRegexp(h.concatRegexp(h.constRegexp("aab"), h.constRegexp("bba")), h.orRegexp(h.constRegexp("aba"), h.constRegexp("bba"))), h.orRegexp(h.concatRegexp(
        h.constRegexp("baa"), h.constRegexp("bba")), h.constRegexp("baa")))), h.concatRegexp(h.orRegexp(h.constRegexp("aaa"), h.concatRegexp(h.orRegexp(h.constRegexp("aaa"), h.constRegexp("abb")), h
        .orRegexp(h.constRegexp("aba"), h.constRegexp("bbb")))), h.concatRegexp(h.orRegexp(h.constRegexp("abb"), h.orRegexp(h.constRegexp("baa"), h.constRegexp("abb"))), h.orRegexp(h.orRegexp(h
        .constRegexp("bbb"), h.constRegexp("bbb")), h.constRegexp("bbb"))))), h.constRegexp("aba"))));
    Constraint c2 = h.regexpConstraint(h.varExpr("v0"), false, h.constRegexp("baa"));
    Constraint c = h.andConstraint(c1, c2);

    h.setSolver(stp());
    Solution solveStp = h.solve(c, 24);

    assertTrue(solveStp.isSatisfiable());
    assertTrue(solveStp.isValidFor(c));
  }

  public void iNACTIVEtestMissingSolution2() throws Exception{
    Hampi h = new Hampi();

    Constraint c = h.andConstraint(h.regexpConstraint(h.varExpr("v0"), true, h.starRegexp(h.concatRegexp(h.constRegexp("aaa"), h.constRegexp("bab")))), h.regexpConstraint(h.varExpr("v0"), false, h
        .orRegexp(h.orRegexp(h.constRegexp("abb"), h.starRegexp(h.orRegexp(h.orRegexp(h.concatRegexp(h.concatRegexp(h.constRegexp("aaa"), h.constRegexp("baa")), h.starRegexp(h.constRegexp("bbb"))), h
            .constRegexp("bab")), h.starRegexp(h.constRegexp("bbb"))))), h.concatRegexp(h.orRegexp(h.orRegexp(h.starRegexp(h.orRegexp(h.concatRegexp(h.constRegexp("aaa"), h.constRegexp("aba")), h
            .constRegexp("bbb"))), h.constRegexp("bab")), h.starRegexp(h.constRegexp("aaa"))), h.orRegexp(h.orRegexp(h.constRegexp("aba"), h.constRegexp("aba")), h.orRegexp(h.starRegexp(h
            .constRegexp("bab")), h.concatRegexp(h.constRegexp("bba"), h.concatRegexp(h.orRegexp(h.constRegexp("aab"), h.constRegexp("aaa")), h.constRegexp("aaa")))))))));
    h.setSolver(stp());
    Solution solveStp = h.solve(c, 20);
    System.out.println("stp:" + solveStp);

    assertTrue(solveStp.isSatisfiable());//the problem stems from the limited var length we consider (min+10)
    assertTrue(solveStp.isValidFor(c));

  }
}
