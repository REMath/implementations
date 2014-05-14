package hampi.tests.parser;

import junit.framework.*;

public class AllParserTests{

  public static Test suite(){
    TestSuite suite = new TestSuite("Test for hampi.tests.parser");
    //$JUnit-BEGIN$
    suite.addTestSuite(HampiWellFormednessTests.class);
    suite.addTestSuite(HampiParsingTests.class);
    //$JUnit-END$
    return suite;
  }

}
