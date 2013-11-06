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

import hampi.Hampi;
import hampi.constraints.*;
import junit.framework.TestCase;

public class ExpressionTests extends TestCase{
  Hampi hampi = new Hampi();

  public void test1() throws Exception{
    Regexp aplusb = hampi.orRegexp(hampi.constRegexp("a"), hampi.constRegexp("b"));
    Regexp aplusbstar = hampi.starRegexp(aplusb);
    Regexp re = hampi.concatRegexp(aplusbstar, hampi.constRegexp("c")); // (a+b)*c
    Expression e = hampi.varExpr("v1");
    Constraint c1 = hampi.regexpConstraint(e, true, re);
    Constraint c = hampi.andConstraint(c1);

    assertEquals(c.getVariables().toString(), 1, c.getVariables().size());
    //bad style to assert on tostring but this is just a smoke test
    assertEquals("VAR(v1) in [[a-b]* . c]", c.toString());
  }

  public void test2() throws Exception{
    Regexp astar = hampi.starRegexp(hampi.constRegexp("a"));
    Regexp b = hampi.constRegexp("b");
    Regexp re = hampi.concatRegexp(astar, b, astar, b, astar); // a* b a* b a* (exactly 2 bs)
    assertEquals("[a* . b . a* . b . a*]", re.toString());
  }

  public void testSubsequenceExpression() throws Exception{
    Regexp aplusb = hampi.orRegexp(hampi.constRegexp("a"), hampi.constRegexp("b"));
    Regexp aplusbstar = hampi.starRegexp(aplusb);
    Regexp re = hampi.concatRegexp(aplusbstar, hampi.constRegexp("c")); // (a+b)*c
    VariableExpression e = hampi.varExpr("v1");
    Expression sub = hampi.subsequenceExpr(e, 2, 3);
    Constraint c1 = hampi.regexpConstraint(sub, true, re);
    Constraint c = hampi.andConstraint(c1);

    assertEquals(c.getVariables().toString(), 1, c.getVariables().size());
    //bad style to assert on tostring but this is just a smoke test
    assertEquals("VAR(v1)[2,3] in [[a-b]* . c]", c.toString());
  }

}
