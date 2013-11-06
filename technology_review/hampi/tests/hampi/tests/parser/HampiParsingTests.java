package hampi.tests.parser;

import hampi.parser.*;
import hampi.utils.Files;

import java.io.*;

import junit.framework.TestCase;

import org.antlr.runtime.*;
import org.antlr.runtime.tree.*;

public class HampiParsingTests extends TestCase{

  public static final String HAMPI_EXAMPLE_DIR = "tests/hampi/tests/parser/";

  public void testLexer() throws Exception{
    lexerTest("example" + 0);
  }

  public void testLexer1() throws Exception{
    lexerTest("example" + 1);
  }

  public void testLexer2() throws Exception{
    lexerTest("example" + 2);
  }

  public void testLexer3() throws Exception{
    lexerTest("example" + 3);
  }

  public void testLexer4() throws Exception{
    lexerTest("example" + 4);
  }

  public void testLexer5() throws Exception{
    lexerTest("example" + 5);
  }

  public void testLexer6() throws Exception{
    lexerTest("example" + 6);
  }

  public void testOr1Lexer() throws Exception{
    lexerTest("testOr1");
  }

  public void testNot1Lexer() throws Exception{
    lexerTest("testNot1");
  }

  public void testParser0() throws Exception{
    parserTest("example" + 0);
  }

  public void testParser1() throws Exception{
    parserTest("example" + 1);
  }

  public void testParser2() throws Exception{
    parserTest("example" + 2);
  }

  public void testParser3() throws Exception{
    parserTest("example" + 3);
  }

  public void testParser4() throws Exception{
    parserTest("example" + 4);
  }

  public void testParser5() throws Exception{
    parserTest("example" + 5);
  }

  public void testParser6() throws Exception{
    parserTest("example" + 6);
  }

  public void testParserEpsilonProduction() throws Exception{
    parserTest("testEpsilonCFGProduction");
  }

  public void testOr1Parser() throws Exception{
    parserTest("testOr1");
  }

  public void testNot1Parser() throws Exception{
    parserTest("testNot1");
  }

  public void testWalker0() throws Exception{
    walkerTest("example" + 0);
  }

  public void testWalker1() throws Exception{
    walkerTest("example" + 1);
  }

  public void testWalker2() throws Exception{
    walkerTest("example" + 2);
  }

  public void testWalker3() throws Exception{
    walkerTest("example" + 3);
  }

  public void testWalker4() throws Exception{
    walkerTest("example" + 4);
  }

  public void testWalker5() throws Exception{
    walkerTest("example" + 5);
  }

  public void testWalker6() throws Exception{
    walkerTest("example" + 6);
  }

  public void testWalkerFull() throws Exception{
    walkerTest("example" + "Full");
  }

  public void testWalkerEpsilonProduction() throws Exception{
    walkerTest("testEpsilonCFGProduction");
  }

  public void testConcat() throws Exception{
    walkerTest("testTypecheck4");
  }

  public void testOr1Walker() throws Exception{
    walkerTest("testOr1");
  }

  public void testNot1Walker() throws Exception{
    walkerTest("testNot1");
  }

  private void lexerTest(Object name) throws IOException,FileNotFoundException{
    String path = HAMPI_EXAMPLE_DIR + name + ".text";

    HampiLexer lexer = new HampiLexer(new ANTLRInputStream(new FileInputStream(path)));

    StringBuilder b = new StringBuilder();
    Token token = lexer.nextToken();
    while (token.getType() != HampiLexer.EOF){
      b.append("\t" + TokenTypes.getTokenType(token.getType()) + "\t\t" + token.getText() + "\n");
      token = lexer.nextToken();
    }
    String expected = Files.getFileContents(path + ".lexing.txt");
    assertNotNull("cannot load " + path + ".lexing.txt", expected);
    assertEquals(expected, b.toString());
  }

  private void parserTest(Object name) throws IOException,FileNotFoundException,RecognitionException{
    String path = HAMPI_EXAMPLE_DIR + name + ".text";

    HampiLexer lexer = new HampiLexer(new ANTLRInputStream(new FileInputStream(path)));
    HampiParser parser = new HampiParser(new CommonTokenStream(lexer));

    CommonTree ast = (CommonTree) parser.program().getTree();
    StringBuilder b = new StringBuilder();
    b.append(ast.toStringTree());
    File resultF = new File(path + ".parsing.txt");
    assertTrue(resultF + " does not exist", resultF.exists());
    assertEquals(Files.getFileContents(path + ".parsing.txt"), b.toString());
  }

  private void walkerTest(Object name) throws IOException,FileNotFoundException,RecognitionException{
    String path = HAMPI_EXAMPLE_DIR + name + ".text";

    checkTreeWalking(path, path);
  }

  private void checkTreeWalking(String inputFile, String expectedOutputFile) throws IOException,FileNotFoundException,RecognitionException{
    HampiLexer lexer = new HampiLexer(new ANTLRInputStream(new FileInputStream(inputFile)));
    HampiParser parser = new HampiParser(new CommonTokenStream(lexer));

    CommonTree ast = (CommonTree) parser.program().getTree();

    // Traverse the tree created by the parser
    CommonTreeNodeStream nodes = new CommonTreeNodeStream(ast);

    HampiTree walker = new HampiTree(nodes);
    StringBuilder b = new StringBuilder();
    b.append(walker.program());
    String buf = b.toString();
    assertEquals(Files.getFileContents(expectedOutputFile), buf);
  }

  //parse just one line
  public void test0() throws Exception{
    String in = "var fred:3;";
    String out = in;
    assertEquals(out, parseAndWalk(in));
  }

  private String parseAndWalk(String stmt) throws Exception{
    HampiLexer lexer = new HampiLexer(new ANTLRInputStream(new ByteArrayInputStream(stmt.getBytes())));
    HampiParser parser = new HampiParser(new CommonTokenStream(lexer));

    CommonTree ast = (CommonTree) parser.program().getTree();
    CommonTreeNodeStream nodes = new CommonTreeNodeStream(ast);

    HampiTree walker = new HampiTree(nodes);
    return String.valueOf(walker.program());
  }

}
