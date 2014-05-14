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

import hampi.grammars.*;
import hampi.grammars.apps.EpsilonProductionRemover;
import hampi.grammars.parser.Parser;
import hampi.utils.*;

import java.io.IOException;
import java.util.*;

import junit.framework.TestCase;

public class EpsilonRemoverTests extends TestCase{
  private static final String DIR = "tests/resources/";

  public void test1() throws Exception{
    defaultTest(1);
  }

  public void test2() throws Exception{
    defaultTest(2);
  }

  public void test3() throws Exception{
    defaultTest(3);
  }

  public void test4() throws Exception{
    defaultTest(4);
  }

  public void test5() throws Exception{
    defaultTest(5);
  }

  public void test6() throws Exception{
    defaultTest(6);
  }

  public void test7() throws Exception{
    defaultTest(7);
  }

  public void test8() throws Exception{
    defaultTest(8);
  }

  public void test9() throws Exception{
    defaultTest(9);
  }

  private void defaultTest(int num) throws IOException{
    Grammar g = new Parser(DIR + "test_epsilons" + num + ".txt").parse();
    new EpsilonProductionRemover().removeEpsilonProductions(g, "S");
    compareIgnoreNewlines(g.toString(), DIR + "test_epsilons" + num + "_expected.txt");
    Set<GrammarProduction> epsilonProductions = EpsilonProductionRemover.getEpsilonProductions(g, g.getNonterminal("S"));
    assertTrue(epsilonProductions.isEmpty());
  }

  public void testDups() throws Exception{
    Grammar g = new Parser(DIR + "test_dups.txt").parse();
    new EpsilonProductionRemover().removeEpsilonProductions(g, "S");
    Set<GrammarProduction> epsilonProductions = EpsilonProductionRemover.getEpsilonProductions(g, g.getNonterminal("S"));
    assertTrue(epsilonProductions.isEmpty());
  }

  public void testECMA() throws Exception{
    Grammar g = new Parser(DIR + "ecmascript.txt").parse();
    new EpsilonProductionRemover().removeEpsilonProductions(g, "FunctionDeclaration");
    Set<GrammarProduction> epsilonProductions = EpsilonProductionRemover.getEpsilonProductions(g, g.getNonterminal("FunctionDeclaration"));
    assertTrue(epsilonProductions.isEmpty());
  }

  public static void compareIgnoreNewlines(String actualContents, String fnameExpected) throws IOException{
    List<String> expectedContentsLines = Files.readWhole(fnameExpected);
    List<String> actualContentsLines = Arrays.asList(actualContents.split("\n|\r\n"));
    assertEquals(CollectionsExt.toStringInLines(expectedContentsLines).trim(), CollectionsExt.toStringInLines(actualContentsLines).trim());
  }

}
