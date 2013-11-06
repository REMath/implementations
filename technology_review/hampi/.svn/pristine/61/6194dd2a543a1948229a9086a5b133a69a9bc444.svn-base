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

import hampi.constraints.*;
import hampi.utils.*;

import java.util.List;

import junit.framework.TestCase;

public class RegexpTests extends TestCase{
  public void testToJavaRegexp0() throws Exception{
    Regexp re = HampiConstraints.constRegexp("a");
    assertEquals("a", re.toJavaRegexpPattern());
  }

  public void testToJavaRegexp1() throws Exception{
    Regexp re = HampiConstraints.orRegexp(HampiConstraints.constRegexp("a"), HampiConstraints.constRegexp("b"));
    assertEquals("[a-b]", re.toJavaRegexpPattern());
    assertTrue("a".matches(re.toJavaRegexpPattern()));
    assertTrue("b".matches(re.toJavaRegexpPattern()));
  }

  public void testToJavaRegexp2() throws Exception{
    Regexp aplusb = HampiConstraints.orRegexp(HampiConstraints.constRegexp("a"), HampiConstraints.constRegexp("b"));
    Regexp re = HampiConstraints.starRegexp(aplusb);
    assertTrue("".matches(re.toJavaRegexpPattern()));
    assertTrue("a".matches(re.toJavaRegexpPattern()));
    assertTrue("b".matches(re.toJavaRegexpPattern()));
    assertTrue("aaaaa".matches(re.toJavaRegexpPattern()));
    assertTrue("abababababaaab".matches(re.toJavaRegexpPattern()));
    assertEquals("([a-b])*", re.toJavaRegexpPattern());
  }

  public void testToJavaRegexp3() throws Exception{
    Regexp aplusb = HampiConstraints.orRegexp(HampiConstraints.constRegexp("a"), HampiConstraints.constRegexp("b"));
    Regexp aplusbstar = HampiConstraints.starRegexp(aplusb);
    Regexp re = HampiConstraints.concatRegexp(aplusbstar, HampiConstraints.constRegexp("c")); // (a+b)*c
    assertTrue("c".matches(re.toJavaRegexpPattern()));
    assertTrue("abaaabc".matches(re.toJavaRegexpPattern()));
    assertTrue(!"abaacab".matches(re.toJavaRegexpPattern()));
    assertEquals("(([a-b])*)(c)", re.toJavaRegexpPattern());
  }

  public void testToJavaRegexp4() throws Exception{
    Regexp aplusb = HampiConstraints.orRegexp(HampiConstraints.constRegexp("a"), HampiConstraints.constRegexp("b"));
    Regexp cplusd = HampiConstraints.orRegexp(HampiConstraints.constRegexp("c"), HampiConstraints.constRegexp("d"));
    Regexp re = HampiConstraints.concatRegexp(aplusb, cplusd); // (a+b)(c+d)
    String java = re.toJavaRegexpPattern();
    System.out.println(java);
    assertTrue("bd".matches(java));
  }

  public void testToJavaRegexp5() throws Exception{
    Regexp aplusb = HampiConstraints.orRegexp(HampiConstraints.constRegexp("a"), HampiConstraints.constRegexp("b"));
    Regexp cplusd = HampiConstraints.orRegexp(HampiConstraints.constRegexp("c"), HampiConstraints.constRegexp("d"));
    Regexp re = HampiConstraints.orRegexp(aplusb, cplusd); // (a+b)+(c+d)
    String java = re.toJavaRegexpPattern();
    System.out.println(java);
    assertTrue("b".matches(java));
  }

  public void testSizeBounds1(){
    Regexp r = HampiConstraints.constRegexp("a");
    assertEquals(1, r.getSizeUpperBound());
    assertEquals(1, r.getSizeLowerBound());
  }

  public void testSizeBounds2() throws Exception{
    Regexp aplusb = HampiConstraints.orRegexp(HampiConstraints.constRegexp("a"), HampiConstraints.constRegexp("b"));
    Regexp cplusd = HampiConstraints.orRegexp(HampiConstraints.constRegexp("c"), HampiConstraints.constRegexp("d"));
    Regexp re = HampiConstraints.orRegexp(aplusb, cplusd); // (a+b)+(c+d)
    assertEquals(1, re.getSizeUpperBound());
    assertEquals(1, re.getSizeLowerBound());
  }

  public void testSizeBounds3() throws Exception{
    Regexp aplusb = HampiConstraints.orRegexp(HampiConstraints.constRegexp("a"), HampiConstraints.constRegexp("b"));
    Regexp aplusbstar = HampiConstraints.starRegexp(aplusb);
    Regexp re = HampiConstraints.concatRegexp(aplusbstar, HampiConstraints.constRegexp("c")); // (a+b)*c
    assertEquals(1, aplusb.getSizeUpperBound());
    assertEquals(Integer.MAX_VALUE, aplusbstar.getSizeUpperBound());
    assertEquals(Integer.MAX_VALUE, re.getSizeUpperBound());
    assertEquals(1, re.getSizeLowerBound());
  }

  public void testSizeBounds4() throws Exception{
    Regexp aplusb = HampiConstraints.orRegexp(HampiConstraints.constRegexp("aa"), HampiConstraints.constRegexp("b"));
    Regexp cplusd = HampiConstraints.orRegexp(HampiConstraints.constRegexp("cccc"), HampiConstraints.constRegexp("d"));
    Regexp re = HampiConstraints.concatRegexp(aplusb, cplusd); // (aa+b).(cccc+d)
    assertEquals(6, re.getSizeUpperBound());
    assertEquals(2, re.getSizeLowerBound());
  }

  public void testRanges() throws Exception{
    char[] chars = { 'a', 'b', '0', '1' };
    List<Pair<Character, Character>> ranges = CollectionsExt.ranges(chars);
    assertEquals(2, ranges.size());
    System.out.println(ranges);
    assertEquals('0', (char) ranges.get(0).first);
    assertEquals('1', (char) ranges.get(0).second);
    assertEquals('a', (char) ranges.get(1).first);
    assertEquals('b', (char) ranges.get(1).second);
  }

  public void testRanges1() throws Exception{
    char[] chars = { 'a', 'c', 'b', '0', '1', '2', '3', '4' };
    List<Pair<Character, Character>> ranges = CollectionsExt.ranges(chars);
    assertEquals(2, ranges.size());
    System.out.println(ranges);
    assertEquals('0', (char) ranges.get(0).first);
    assertEquals('4', (char) ranges.get(0).second);
    assertEquals('a', (char) ranges.get(1).first);
    assertEquals('c', (char) ranges.get(1).second);
  }

  public void testRanges2() throws Exception{
    char[] chars = { 'a', 'c', 'b', 'd', 'e', 'f' };
    List<Pair<Character, Character>> ranges = CollectionsExt.ranges(chars);
    assertEquals(1, ranges.size());
    System.out.println(ranges);
    assertEquals('a', (char) ranges.get(0).first);
    assertEquals('f', (char) ranges.get(0).second);
  }

}
