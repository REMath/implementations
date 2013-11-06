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
import hampi.tests.AllHampiTests;
import hampi.tests.gramgren.AllGramgenTests;
import hampi.tests.parser.AllParserTests;
import junit.framework.*;

public class AllTests{

  public static Test suite(){
    TestSuite suite = new TestSuite("Hampi string solver");
    suite.addTest(AllHampiTests.suite());
    suite.addTest(AllGramgenTests.suite());
    suite.addTest(AllParserTests.suite());
    return suite;
  }

  public static void main(String[] args){
    //Different UIs
    //    junit.textui.TestRunner.run(AllTests.suite());
    //    TestRunner.run(AllTests.class);
    junit.swingui.TestRunner.run(AllTests.class);
  }

}
