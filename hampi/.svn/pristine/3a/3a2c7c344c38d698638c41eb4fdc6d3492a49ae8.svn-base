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
import hampi.grammars.apps.CNFConverter;
import hampi.grammars.cykparser.*;
import hampi.grammars.parser.Parser;

import java.util.*;

import junit.framework.TestCase;

public class CYKTests extends TestCase{
  public void test1() throws Exception{
    String grammarFile = "tests/resources/test_cyk1.txt";
    Grammar g = new Parser(grammarFile).parse();
    System.out.println(g);
    CYKParser p = new CYKParser(g);
    List<ParseTree> parse = p.parse("s1 s2".split(" "), "S");
    assertTrue(!parse.isEmpty());
  }

  public void test2() throws Exception{
    String grammarFile = "tests/resources/test_cyk1.txt";
    Grammar g = new Parser(grammarFile).parse();
    System.out.println(g);
    CYKParser p = new CYKParser(g);
    List<ParseTree> parse = p.parse("s1 s2 s1".split(" "), "S");
    assertTrue(parse.isEmpty());
  }

  public void test3() throws Exception{
    String grammarFile = "tests/resources/test_cyk2.txt";
    Grammar g = new Parser(grammarFile).parse();
    System.out.println(g);
    CYKParser p = new CYKParser(g);
    String s = "b a a b a";
    List<ParseTree> parse = p.parse(s.split(" "), "S");
    System.out.println(s);
    System.out.println(parse);
    assertTrue(!parse.isEmpty());
  }

  public void test4() throws Exception{
    String grammarFile = "tests/resources/test_cyk2.txt";
    Grammar g = new Parser(grammarFile).parse();
    System.out.println(g);
    CYKParser p = new CYKParser(g);
    String s = "b a b a";
    List<ParseTree> parse = p.parse(s.split(" "), "S");
    assertTrue(parse.toString(), parse.isEmpty());
  }

  public void test5() throws Exception{
    String grammarFile = "tests/resources/test_cyk3.txt";
    Grammar g = new Parser(grammarFile).parse();
    System.out.println(g);
    CYKParser p = new CYKParser(g);
    String s = "a b b d a b";
    List<ParseTree> parse = p.parse(s.split(" "), "S");
    assertTrue(!parse.isEmpty());
  }

  public void test6() throws Exception{
    String grammarFile = "tests/resources/test_cyk3.txt";
    Grammar g = new Parser(grammarFile).parse();
    System.out.println(g);
    CYKParser p = new CYKParser(g);
    String s = "b a d";
    List<ParseTree> parse = p.parse(s.split(" "), "S");
    assertTrue(parse.toString(), parse.isEmpty());
  }

  public void testEcmascript1() throws Exception{
    String grammarFile = "tests/resources/ecmascript.txt";
    Grammar g = new Parser(grammarFile).parse();
    assertTrue(!g.isCNF());

    List<Grammar> steps = new ArrayList<Grammar>();
    final String startSymbol = "FunctionDeclaration";
    Grammar gCNF = new CNFConverter().convertToCNF(g, startSymbol, steps);

    CYKParser p = new CYKParser(gCNF);
    String s = "function <IDENTIFIER_NAME> ( ) { break ; }";
    List<ParseTree> parse = p.parse(s.split(" "), startSymbol);
    assertTrue("cannot parse: " + s, !parse.isEmpty());
  }

  public void testEcmascript2() throws Exception{
    String grammarFile = "tests/resources/test_cyk_ecmascript.txt";
    Grammar g = new Parser(grammarFile).parse();
    assertTrue(!g.isCNF());

    List<Grammar> steps = new ArrayList<Grammar>();
    final String startSymbol = "FunctionDeclaration";
    Grammar gCNF = new CNFConverter().convertToCNF(g, startSymbol, steps);

    CYKParser p = new CYKParser(gCNF);
    String s = "function <IDENTIFIER_NAME> ( ) { break ; }";
    List<ParseTree> parse = p.parse(s.split(" "), startSymbol);
    assertTrue("cannot parse: " + s, !parse.isEmpty());
  }

  public void testEcmascript3() throws Exception{
    String grammarFile = "tests/resources/test_cyk_ecmascript1.txt";
    Grammar g = new Parser(grammarFile).parse();
    assertTrue(!g.isCNF());

    List<Grammar> steps = new ArrayList<Grammar>();
    final String startSymbol = "FunctionDeclaration";
    Grammar gCNF = new CNFConverter().convertToCNF(g, startSymbol, steps);

    CYKParser p = new CYKParser(gCNF);
    String s = "break ; ";
    List<ParseTree> parse = p.parse(s.split(" "), startSymbol);
    assertTrue("cannot parse: " + s, !parse.isEmpty());
  }

  public void testEcmascript4() throws Exception{
    String grammarFile = "tests/resources/ecmascript.txt";
    Grammar g = new Parser(grammarFile).parse();
    assertTrue(!g.isCNF());

    List<Grammar> steps = new ArrayList<Grammar>();
    final String startSymbol = "FunctionDeclaration";
    Grammar gCNF = new CNFConverter().convertToCNF(g, startSymbol, steps);

    CYKParser p = new CYKParser(gCNF);
    String s = "function <IDENTIFIER_NAME> ( ) { -- <HEX_INTEGER_LITERAL> >= - <STRING_LITERAL> typeof true , false }";
    List<ParseTree> parse = p.parse(s.split(" "), startSymbol);
    for (ParseTree parseTree : parse){
      System.out.println(parseTree.toString());
    }
    assertTrue("cannot parse: " + s, !parse.isEmpty());
  }

  public void testEcmascript5() throws Exception{
    String grammarFile = "tests/resources/ecmascript.txt";
    Grammar g = new Parser(grammarFile).parse();
    assertTrue(!g.isCNF());

    List<Grammar> steps = new ArrayList<Grammar>();
    final String startSymbol = "Statement";
    Grammar gCNF = new CNFConverter().convertToCNF(g, startSymbol, steps);

    CYKParser p = new CYKParser(gCNF);
    String s = "-- <HEX_INTEGER_LITERAL> >= - <STRING_LITERAL>";
    List<ParseTree> parse = p.parse(s.split(" "), startSymbol);
    for (ParseTree parseTree : parse){
      System.out.println(parseTree.toString());
    }
    assertTrue("cannot parse: " + s, !parse.isEmpty());
  }

  public void testEcmascript6() throws Exception{
    String grammarFile = "tests/resources/ecmascript.txt";
    Grammar g = new Parser(grammarFile).parse();
    assertTrue(!g.isCNF());

    List<Grammar> steps = new ArrayList<Grammar>();
    final String startSymbol = "Expression";
    Grammar gCNF = new CNFConverter().convertToCNF(g, startSymbol, steps);

    CYKParser p = new CYKParser(gCNF);
    String s = "typeof true , false";
    List<ParseTree> parse = p.parse(s.split(" "), startSymbol);
    for (ParseTree parseTree : parse){
      System.out.println(parseTree.toString());
    }
    assertTrue("cannot parse: " + s, !parse.isEmpty());
  }

  public void testEcmascript7() throws Exception{
    String grammarFile = "tests/resources/ecmascript.txt";
    Grammar g = new Parser(grammarFile).parse();
    assertTrue(!g.isCNF());

    List<Grammar> steps = new ArrayList<Grammar>();
    final String startSymbol = "AssignmentExpression";
    Grammar gCNF = new CNFConverter().convertToCNF(g, startSymbol, steps);

    CYKParser p = new CYKParser(gCNF);
    String s = "typeof true";
    List<ParseTree> parse = p.parse(s.split(" "), startSymbol);
    for (ParseTree parseTree : parse){
      System.out.println(parseTree.toString());
    }
    assertTrue("cannot parse: " + s, !parse.isEmpty());
  }

  public void testEcmascript8() throws Exception{
    String grammarFile = "tests/resources/ecmascript.txt";
    Grammar g = new Parser(grammarFile).parse();
    assertTrue(!g.isCNF());

    List<Grammar> steps = new ArrayList<Grammar>();
    final String startSymbol = "AssignmentExpression";
    Grammar gCNF = new CNFConverter().convertToCNF(g, startSymbol, steps);

    CYKParser p = new CYKParser(gCNF);
    String s = "false";
    List<ParseTree> parse = p.parse(s.split(" "), startSymbol);
    for (ParseTree parseTree : parse){
      System.out.println(parseTree.toString());
    }
    assertTrue("cannot parse: " + s, !parse.isEmpty());
  }

}
