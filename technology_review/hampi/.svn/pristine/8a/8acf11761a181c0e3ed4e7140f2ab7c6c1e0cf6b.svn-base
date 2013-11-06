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
package hampi.tests.gramgren;

import hampi.grammars.Grammar;
import hampi.grammars.apps.*;
import hampi.grammars.parser.Parser;
import hampi.utils.*;

import java.io.IOException;
import java.util.*;

import junit.framework.TestCase;

public class GrammarTests extends TestCase{

  public static final String DIR = "tests/resources/";

  public void testCopy1() throws Exception{
    Grammar g = new Parser(DIR + "test_cyk1.txt").parse();
    Grammar g1 = g.makeCopy();
    assertEquals(g.toString(), g1.toString());
    assertEquals(g, g1);
    assertTrue(g != g1);
  }

  public void testCopy2() throws Exception{
    Grammar g = new Parser(DIR + "ecmascript.txt").parse();
    Grammar g1 = g.makeCopy();
    assertEquals(g.toString(), g1.toString());
    assertEquals(g, g1);
    assertTrue(g != g1);
  }

  public void testCNF1() throws Exception{
    checkCNF("test_cyk1.txt", "S");
  }

  public void testCNF2() throws Exception{
    checkCNF("test_cyk2.txt", "S");
  }

  public void testCNF3() throws Exception{
    checkCNF("test_cyk3.txt", "S");
  }

  public void testNonCNF1() throws IOException{
    checkNonCNF("test_expose.txt", "A");
  }

  public void testNonCNF2() throws IOException{
    checkNonCNF("test_expose2.txt", "A");
  }

  public void testNonCNF3() throws IOException{
    checkNonCNF("test_inlining.txt", "S");
  }

  public void testNonCNF4() throws IOException{
    checkNonCNF("test_inlining_2.txt", "S");
  }

  public void testNonCNF7() throws IOException{
    checkNonCNF("test_generate1.txt", "S");
  }

  //
  //   public void testNonCNF8() throws IOException{
  //      checkNonCNF("test_unreachable.txt", "S");
  //   }

  public void testNonCNF9() throws IOException{
    checkNonCNF("test_dups.txt", "S");
  }

  public void testNonCNF10() throws IOException{
    checkNonCNF("test_dups1.txt", "S");
  }

  public void testNonCNF11() throws IOException{
    checkNonCNF("test_plus.txt", "S");
  }

  public void testNonCNF12() throws IOException{
    checkNonCNF("test_options.txt", "S");
  }

  //   public void testNonCNF13() throws IOException{
  //      checkNonCNF("test_star.txt", "S");
  //   }

  public void testNonCNF15() throws IOException{
    checkNonCNF("test_generate.txt", "expr");
  }

  public void testNonCNF16() throws Exception{
    checkNonCNF("ecmascript.txt", "FunctionDeclaration");
  }

  public void testNonCNF17() throws Exception{
    checkNonCNF("expr.txt", "expr");
  }

  public void testNonCNF18() throws Exception{
    Grammar g = new Parser(DIR + "test_cnf1.txt").parse();
    assertTrue(!g.isCNF());

    List<Grammar> steps = new ArrayList<Grammar>();
    Grammar gCNF = new CNFConverter().convertToCNF(g, "S", steps);

    System.out.println("orig :\n" + g);
    System.out.println("step0:\n" + steps.get(0));
    System.out.println("step1:\n" + steps.get(1));
    compareIgnoreNewlines(steps.get(1).toString(), DIR + "test_cnf1_step1_expected.txt");

    System.out.println("step2:\n" + steps.get(2));
    compareIgnoreNewlines(steps.get(2).toString(), DIR + "test_cnf1_step2_expected.txt");

    System.out.println("step3:\n" + steps.get(3));
    compareIgnoreNewlines(steps.get(3).toString(), DIR + "test_cnf1_step3_expected.txt");

    System.out.println("step4:\n" + steps.get(4));
    compareIgnoreNewlines(steps.get(4).toString(), DIR + "test_cnf1_step4_expected.txt");

    System.out.println("step5:\n" + gCNF);

    assertEquals(5, steps.size());
    compareIgnoreNewlines(gCNF.toString(), DIR + "test_cnf1_expected.txt");

    assertTrue("Not in CNF\n" + gCNF.toString(), gCNF.isCNF());

  }

  public void testNonCNF19() throws Exception{
    Grammar gCNF = checkNonCNF("test_cyk_ecmascript1.txt", "FunctionDeclaration");
    System.out.println(gCNF);
  }

  public void testReplace1() throws Exception{
    Grammar g = new Parser(DIR + "test_replace1.txt").parse();
    GrammarElementReplacer ger = new GrammarElementReplacer(g.getNonterminal("X"), g.getNonterminal("S"));
    g.accept(ger);
    compareIgnoreNewlines(g.toString(), DIR + "test_replace1_expected.txt");
  }

  //----------------------------------------------------------------------
  private Grammar checkNonCNF(String string, String start) throws IOException{
    Grammar g = new Parser(DIR + string).parse();
    assertTrue(!g.isCNF());

    Grammar gCNF = new CNFConverter().convertToCNF(g, start);
    assertTrue("not in CNF:\n" + gCNF, gCNF.isCNF());
    return gCNF;
  }

  private void checkCNF(String string, String start) throws IOException{
    Grammar g = new Parser(DIR + string).parse();
    assertTrue(g.isCNF());

    Grammar gCNF = new CNFConverter().convertToCNF(g, start);
    assertEquals(g, gCNF);
    assertTrue(gCNF.isCNF());
  }

  public static void compareIgnoreNewlines(String actualContents, String fnameExpected) throws IOException{
    List<String> expectedContentsLines = Files.readWhole(fnameExpected);
    List<String> actualContentsLines = Arrays.asList(actualContents.split("\n|\r\n"));
    assertEquals(CollectionsExt.toStringInLines(expectedContentsLines).trim(), CollectionsExt.toStringInLines(actualContentsLines).trim());
  }

}
