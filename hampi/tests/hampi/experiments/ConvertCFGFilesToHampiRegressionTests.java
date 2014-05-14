package hampi.experiments;

import static hampi.experiments.HampiExperiments.*;
import hampi.utils.*;

import java.io.*;
import java.util.*;

/**
 * This utility takes cfg files and generates hampi regression tests.
 */
public class ConvertCFGFilesToHampiRegressionTests{
  /**
   * This is where tests are created.
   */
  private static final String TEST_DIR = "tests/hampi/tests";

  /**
   * Arguments: filename with lists of file names (with cfg grammars).
   */
  public static void main(String[] args) throws IOException{
    List<List<String>> fnamepairs = HampiExperiments.listPerLine(args[0]);

    convertCFGFilesToEmptinessRegressionTests(20, fnamepairs);
    convertCFGFilePairsToRegressionTests(fnamepairs, 5, 200);//intersection
  }

  /**
   * Creates Hampi regression tests from cfg files (grammar emptiness tests).
   * Assumes each list contains list one element.
   */
  private static void convertCFGFilesToEmptinessRegressionTests(int size, List<List<String>> fnamepairs) throws IOException{
    for (List<String> fnamelist : fnamepairs){
      String fname = fnamelist.get(0);
      if (skipFile(fname)){
        continue;
      }
      if (!HAMPI_VERY_SLOW.contains(fname)){
        continue;
      }

      File cfgFile = new File(fname);
      String membershipConstraint = CFG2HMP.convertToEmptinessConstraint(size, cfgFile.getAbsolutePath());
      String fnameNoExtension = fname.substring(0, fname.lastIndexOf(".cfg"));
      //      System.out.println(fname);
      //      System.out.println(format);
      //      System.out.println(fnameNoExtension);
      String hampiFileName = "cfg_" + fnameNoExtension.replace('-', '_') + "_" + size;
      String hampiFileContent = "//created from CFGAnalyzer file " + cfgFile.getName() + " (see there for origin info)" + Utils.newLine + membershipConstraint;
      Files.writeToFile(hampiFileContent, TEST_DIR + "/test_" + hampiFileName + ".hmp");
      System.out.println("/** Test created by converting a CFGAnalyzer example to hampi grammar membership constraint for size " + size + ". */");
      System.out.println("public void test_" + hampiFileName + "() throws Exception{");

      Pair<Boolean, Double> p = CFGAnalyzer.runEmptiness(size, null, cfgFile);
      System.out.println("   doTest(" + p.first + ", 0);");
      System.out.println("}");
      System.out.println("");
    }
  }

  /**
   * Creates Hampi regression tests from pairs or cfg files (e.g., grammar
   * intersection tests).
   */
  private static void convertCFGFilePairsToRegressionTests(List<List<String>> fnamepairs, int size, int createHowMany) throws IOException{
    List<String> createdFiles = new ArrayList<String>();
    boolean expectSat = true;
    for (List<String> pair : fnamepairs){
      if (createdFiles.size() > createHowMany){//we want this many tests
        break;
      }
      String fname1 = pair.get(0);
      String fname2 = pair.get(1);
      if (skipFile(fname1) || skipFile(fname2)){
        continue;
      }
      File f1 = new File(fname1);
      File f2 = new File(fname2);
      StringBuilder out = new StringBuilder();
      Pair<Boolean, Double> res = CFGAnalyzer.runIntersection(size, out, f1, f2);
      boolean actualSat = res.first;
      if (actualSat == expectSat){
        String hampi = CFG2HMP.convertToIntersectionConstraint(size, f1.getAbsolutePath(), f2.getAbsolutePath());
        hampi = "/*" + out.toString() + "*/\n" + hampi;
        String hampiFileName = "test_" + simpleFileName(fname1) + "_AND_" + simpleFileName(fname2) + "_size" + size;
        System.out.println("/** Intersection constraint from files  " + pair.toString() + " for size " + size + ".*/");
        System.out.println("public void " + hampiFileName + "() throws Exception{");
        System.out.println(" doTest(" + actualSat + ", Double.MAX_VALUE);");
        System.out.println("}");
        Files.writeToFile(hampi, TEST_DIR + "/" + hampiFileName + ".hmp");
        createdFiles.add(hampiFileName);

        expectSat = !expectSat;//flip the expectation - we want equal number of sat and unsat tests

      }
    }
  }

  /**
   * filename.cfg -> filename
   */
  private static String simpleFileName(String fname1){
    return fname1.substring(0, fname1.length() - 4);
  }
}
