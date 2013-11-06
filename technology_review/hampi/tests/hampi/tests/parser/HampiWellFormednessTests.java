package hampi.tests.parser;

import hampi.parser.*;
import junit.framework.TestCase;

public class HampiWellFormednessTests extends TestCase{
  private static final String P = HampiParsingTests.HAMPI_EXAMPLE_DIR;

  private void checkFail(String path, String reason) throws Exception{
    HProgram ast = HProgramParser.parse(P + path);
    assertNotNull(ast);
    String checkWellFormedness = HProgramParser.checkWellFormedness(ast);
    if (checkWellFormedness == null){
      fail("expected to fail well-formedness test " + reason + "  " + path);
    }
    assertEquals(reason, checkWellFormedness);
  }

  private void checkPass(String path) throws Exception{
    HProgram ast = HProgramParser.parse(P + path);
    assertNotNull(ast);
    HProgramParser.checkWellFormedness(ast);
  }

  public void testZeroVars() throws Exception{
    checkFail("testVar0.txt", "no string variable declared");
  }

  public void testTwoVars() throws Exception{
    checkFail("testVar2.txt", "more than one string variable declared x y");
  }

  public void testNoAsserts() throws Exception{
    checkFail("testNoAsserts.txt", "at least one assert expected");
  }

  public void testNamesDefined1() throws Exception{
    checkFail("testNamesDefined1.txt", "undefined nonterminal B");
  }

  public void testNamesDefined2() throws Exception{
    checkFail("testNamesDefined2.txt", "undefined variable v in 'contains'");
  }

  public void testNamesDefined3() throws Exception{
    checkFail("testNamesDefined3.txt", "B not of type CFG_TYPE");
  }

  public void testNamesDefined4() throws Exception{
    checkFail("testNamesDefined4.txt", "extected string type on left in 'in' but got null in v in R");
  }

  public void testNamesDefined5() throws Exception{
    checkFail("testNamesDefined5.txt", "extected reg or cfg type on right in 'in' but got null in x in S");
  }

  public void testNonterminalsDefinedOnce() throws Exception{
    checkFail("testNonterminalsDefinedOnce.txt", "multiply defined variable A");
  }

  public void testNonterminals() throws Exception{
    checkFail("testNonterminals.txt", "expected a nonterminal x");
  }

  public void testTypecheck() throws Exception{
    checkFail("testTypecheck.txt", "x not of type CFG_TYPE");
  }

  public void testTypecheck1() throws Exception{
    checkPass("testTypecheck1.txt");
  }

  public void testTypecheckFul() throws Exception{
    checkPass("exampleFull.text");
  }

  public void testTypecheck2() throws Exception{
    checkPass("testTypecheck2.txt");
  }

  public void testTypecheck3() throws Exception{
    checkPass("testTypecheck3.txt");
  }

  public void testTypecheck4() throws Exception{
    checkPass("testTypecheck4.text");
  }

  public void testTypecheckToLongSubsequence() throws Exception{
    checkFail("testTypecheck5.txt", "subsequence cannot end after the variable ends");
  }

}
