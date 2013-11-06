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
import hampi.stp.STPSolver;
import hampi.utils.*;
import junit.framework.TestCase;

public class RandomSolverTests extends TestCase{

  public void testSTPSolver() throws Exception{
    long seed = System.currentTimeMillis();
    System.out.println("seed:" + seed);
    Randomness.reset(seed);
    for (int i = 0; i < 100; i++){
      Hampi h = new Hampi();
      h.setSolver(new STPSolver());

      Constraint c = null;
      Solution solSTP = null;
      Solution solMona = null;
      try{
        //        System.out.println("-------------------------------------------");
        System.out.println(" " + i);
        int size = 1 + Randomness.nextRandomInt(2);
        Constraint[] cs = new Constraint[size];
        int varNum = 1;//just 1 var
        cs[0] = randomConstraint(varNum, h);
        for (int j = 1; j < cs.length; j++){
          cs[j] = randomConstraint(varNum, h);
        }
        c = h.andConstraint(cs);
        System.out.println("-----------------------------------------------");
        System.out.println(c.toJavaCode("h"));
        System.out.println();

        h.setSolver(new STPSolver());
        StopWatch sw = new StopWatch("Solving");
        sw.start();
        solSTP = h.solve(c, 10);
        sw.stop();
        System.out.println(sw);
        System.out.println("stp solution: " + solSTP);
        //        System.out.println(sol);
      }catch (RuntimeException e){
        if (c != null){
          e.printStackTrace();
          System.out.println("================================================");
          System.out.println("ERROR solving constraint:\n");
          System.out.println(c);
          System.out.println(c.toJavaCode("h"));
          System.out.println(solSTP);
          System.out.println("================================================");
          throw e;
        }
      }
    }

  }

  private Constraint randomConstraint(int varNum, Hampi hs){
    int idx = varNum == 1 ? 0 : Randomness.nextRandomInt(varNum);
    Expression v = HampiConstraints.varExpr("v" + idx);
    return HampiConstraints.regexpConstraint(v, Randomness.nextRandomBool(), randomRegexp(hs));
  }

  private Regexp randomRegexp(Hampi hs){
    int choice = Randomness.nextRandomInt(4);
    int depth = new Throwable().getStackTrace().length;
    //    System.out.println("dep:" + depth);
    if (depth > 25){
      choice = 0;
    }
    switch (choice){
    case 0:
      return hs.constRegexp(Randomness.nextRandomString(3, 'a', 'b'));
    case 1: {
      Regexp e1 = randomRegexp(hs);
      Regexp e2 = randomRegexp(hs);
      return hs.concatRegexp(e1, e2);
    }
    case 2: {
      Regexp e1 = randomRegexp(hs);
      Regexp e2 = randomRegexp(hs);
      return hs.orRegexp(e1, e2);
    }
    case 3: {
      Regexp e1 = randomRegexp(hs);
      return hs.starRegexp(e1);
    }
    }
    throw new IllegalStateException();
  }
  //  ICollector<String> printer = new ICollector<String>(){
  //                               public void collect(String t){
  //                                 System.out.println(t);
  //                               }
  //                             };
  //
  //  public void test2() throws IOException{
  //    Grammar g = new Parser("expr.txt").parse();
  //    new UniformStringGenerator(4, g, null, "T").generate(10, printer);
  //  }
}
