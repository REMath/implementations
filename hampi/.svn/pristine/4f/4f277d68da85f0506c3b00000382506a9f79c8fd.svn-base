package hampi.tests;

import hampi.*;
import hampi.utils.*;

import java.io.*;
import java.text.DecimalFormat;

import junit.extensions.TestSetup;
import junit.framework.*;

import org.antlr.runtime.RecognitionException;

public class FullSolverTests extends TestCase{
  private static final String PORT = String.valueOf(4444);
  public static final String D = "tests/hampi/tests/";
  private static final boolean IGNORE_TIMES = true;
    private static final boolean CLIENT = false;//true;
  private static final boolean DEBUG = false;//if true, run hampi in the same VM so that you can set up breakpoints
  private static boolean serverRunning = false;

  public static Test suite(){
    return new TestSetup(new TestSuite(FullSolverTests.class)){
      @Override
      protected void setUp() throws Exception{
        if (!CLIENT || serverRunning)
          return;
        int exec = Command.exec(new String[] { "/bin/bash", "hampi_server.sh", PORT }, null);
        File hampiServer = new File(HampiServer.HAMPISERVER_RUNNING);
        hampiServer.deleteOnExit();
        int count = 5;
        while (count > 0 && !hampiServer.exists()){
          Thread.sleep(500);//wait for the server to start
          count--;
        }
        if (count == 0 || exec != 0){
          System.err.println("Cannot start hampi server on port " + PORT);
        }else{
          serverRunning = true;
        }
      }

      @Override
      protected void tearDown() throws Exception{
        if (!CLIENT || !serverRunning)
          return;
        OutputStream os = new ByteArrayOutputStream();
        PrintStream out = new PrintStream(os);
        int exec = Command.exec(new String[] { "/bin/bash", "hampi_client.sh", PORT, "SHUTDOWN" }, out);
        System.out.println(os);
        if (exec != 0)
          throw new IllegalStateException(os.toString());
        serverRunning = false;
      }
    };
  }

  /**
   * Returns sat/unsat and time in milliseconds. Creates a separate VM instance
   * every time. This is very slow but makes a fairer comparison with
   * CFGAnalyzer.
   */
  private static Pair<Boolean, Long> solveConstraintNewVM(String fname){
    ByteArrayOutputStream os = new ByteArrayOutputStream();
    PrintStream blackHole = new PrintStream(os);
    StopWatch w = new StopWatch("");
    w.start();
    String verbose = "";//"-v" if verbose
	int exec = Command.exec(new String[] { "/bin/bash", "hampi.sh", fname, verbose }, blackHole);
    w.stop();
    if (exec != 0 && exec != 1){
      System.err.println("exit " + exec + "\n" + os);
      fail("unusual exit code:" + exec + "\n" + os);
    }
    System.out.println(os);
    return Pair.create(exec == 0, w.getTotal());
  }

  /**
   * Returns sat/unsat and time in milliseconds. Calls to a separate VM that
   * runs a Hampi server.
   */
  private static Pair<Boolean, Long> solveConstraint_client(String fname){
    ByteArrayOutputStream os = new ByteArrayOutputStream();
    PrintStream out = new PrintStream(os);
    StopWatch w = new StopWatch("");
    w.start();
    int exec = Command.exec(new String[] { "/bin/bash", "hampi_client.sh", PORT, fname }, out);
    w.stop();
    if (exec != 0 && exec != 1){
      System.err.println(os);
      fail(os.toString());
    }
    System.out.println(fname + " " + os);
    if (os.toString().contains("ERROR")){
      fail(os.toString());
    }
    boolean isUNSAT = os.toString().contains("UNSAT");
    return Pair.create(!isUNSAT, w.getTotal());
  }

  private static Pair<Boolean, Long> solveConstraintInPlace(String fname) throws IOException{
    StopWatch w = new StopWatch("");
    w.start();
    boolean isSat = false;
    try{
      InputStream istream = new ByteArrayInputStream(Files.getFileContents(fname).getBytes());
      Hampi.run(false, true, istream);
      isSat = true;
    }catch (HampiResultException e){
      if (e.getExitCode() == HampiResultException.CODE_UNSAT){
        isSat = false;
      }else
        throw new IllegalStateException(e);
    }catch (RecognitionException e){
      throw new IllegalStateException(e);
    }
    w.stop();
    return Pair.create(isSat, w.getTotal());
  }

  private static Solution solve(String fname) throws Exception{
    InputStream istream = new ByteArrayInputStream(Files.getFileContents(fname).getBytes());
    return Hampi.run(false, true, istream);
  }

  /**
   * there are two modes: baseline time collection and checking.
   */
  private void doTest(boolean extectedSAT, double timeLimit) throws Exception{
    System.out.println();
    boolean RECOMPUTE_BASELINE_TIMES = false;

    //repeat the run this many times, to get mean solving time
    int repeat = RECOMPUTE_BASELINE_TIMES ? 3 : 1;

    double time;
    boolean sat = false;

    long[] times = new long[repeat];
//    System.out.println(Files.getFileContents(D + getName() + ".hmp"));
    for (int r = 0; r < repeat; r++){
      Pair<Boolean, Long> solveConstraint;
      if (serverRunning){
        solveConstraint = solveConstraint_client(D + getName() + ".hmp");
      }else if (DEBUG){
        solveConstraint = solveConstraintInPlace(D + getName() + ".hmp");
      }else{
        solveConstraint = solveConstraintNewVM(D + getName() + ".hmp");
      }
      times[r] = solveConstraint.second;
      sat = solveConstraint.first;
    }
    time = CollectionsExt.mean(times);
    assertEquals(extectedSAT, sat);
    if (IGNORE_TIMES)
      return;

    if (RECOMPUTE_BASELINE_TIMES){
      if (getName().startsWith("test_cfg")){
        System.out.println("/**");
        System.out.println("* Test created by converting a CFGAnalyzer example to hampi grammar");
        System.out.println("* membership constraint for size 7.");
        System.out.println("*/");
      }
      DecimalFormat df = new DecimalFormat("####.##");
      System.out.println("public void " + getName() + "() throws Exception{");
      System.out.println(" doTest(" + extectedSAT + ", " + df.format(time) + ");");
      System.out.println("}");
      System.out.println();
    }else{
      double flexibility = 2.0;
      double flexibleUpperLimit = timeLimit == Double.MAX_VALUE ? Double.MAX_VALUE : (timeLimit < 1000 ? 2000 : timeLimit * flexibility);
      assertTrue("time limit exceeded expected " + flexibleUpperLimit + " got " + time, flexibleUpperLimit >= time);
      double flexibleLowerLimit = timeLimit == Double.MAX_VALUE ? 0 : (timeLimit < 1000 ? 100 : timeLimit * (1 / flexibility));
      if (time <= flexibleLowerLimit){//catch is faster than 3x what is expected
        fail("solving got faster was:" + timeLimit + " got " + time);
      }
    }
  }

  //This takes 78s seconds (in Adam's VM), 77 sec are in grammar bounding. The grammar has 37539 productions
  public void DISABLEtestWSU23_0_1() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testPaperExample() throws Exception{
      doTest(true, Double.MAX_VALUE);
  }

  public void testSubsequence1() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testSubsequence2() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  public void testSubsequence3() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testSubsequence4() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testEquals1() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testEquals2() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testEquals3() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testEquals4() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  public void testEquals5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testEquals6() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testEquals7() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testMultipleOccurencesOFVariableInConcat() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testMinMaxSize1() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testMinMaxSize() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testBoundInference1() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testBoundInference2() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testBoundInference3() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  public void testBoundInference4() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testRegression5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testWSU1_3_3() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testWSU3_0() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testWSU3_1() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testWSU3_2() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testWSU3_3() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testWSU3_4() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testWSU3_5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testWSU3_6() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testWSU3_7() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  public void testWSU3_8() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  public void testWSU3_9() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  public void testWSU3_10() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }
  /** Intersection constraint from file 013.cfg and 045.cfg for size 5. */
  public void test_013_AND_045_size3() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void testSolveNotIn1() throws Exception{
    Solution solve = solve(D + getName() + ".hmp");
    assertEquals("b", solve.getValueForVar("v"));
  }

  public void testSolveNotContains1() throws Exception{
    Solution solve = solve(D + getName() + ".hmp");
    assertEquals("b", solve.getValueForVar("v"));
  }

  public void testCharEncodingFormat() throws Exception{
    doTest(true, 0);
  }

  /**
   * This test used to be very slow (before we cached permutations more
   * aggressively).
   */
  public void testFixedPrefix1() throws Exception{
    doTest(false, 0);
  }

  public void testFixedPrefix2() throws Exception{
    doTest(true, 0);
  }

  public void testSolve1() throws Exception{
    doTest(true, 234.33);
  }

  public void testSolve2() throws Exception{
    doTest(true, 355.67);
  }

  public void testSolve3() throws Exception{
    doTest(true, 319);
  }

  public void testSolve4() throws Exception{
    doTest(true, 246.33);
  }

  public void testSolve5() throws Exception{
    doTest(true, 240);
  }

  public void testSolve6() throws Exception{
    doTest(true, 251.67);
  }

  public void testSolve7() throws Exception{
    doTest(true, 232.67);
  }

  public void testSolve8() throws Exception{
    doTest(true, 252.67);
  }

  public void testSolve9() throws Exception{
    doTest(true, 232.67);
  }

  public void testSolve10() throws Exception{
    doTest(true, 236.67);
  }

  public void testSolve11() throws Exception{
    doTest(true, 276);
  }

  public void testSolve12() throws Exception{
    doTest(true, 298.67);
  }

  public void testSolveCFG1() throws Exception{
    doTest(true, 368);
  }

  public void testSolveCFG2() throws Exception{
    doTest(true, 411.33);
  }

  public void testSolveCFG3() throws Exception{
    doTest(true, 304.33);
  }

  public void testSolveVal1() throws Exception{
    doTest(true, 287.33);
  }

  public void testSolveVal2() throws Exception{
    doTest(true, 269);
  }

  public void testRegression1() throws Exception{
    doTest(true, 306.33);
  }

  //this used to fail because we counted every terminal as 1 string
  public void testRegression3() throws Exception{
    doTest(true, 0);
  }

  public void testRegression4() throws Exception{
    doTest(true, 0);
  }

  /**
   * Intersection constraint from files [resources/othertools/ambiguity/034.cfg,
   * resources/othertools/ambiguity/050.cfg] for size 24.
   */
  public void test_034_AND_050_size24() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  public void test_034_size24() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  public void test_050_size24() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 047.cfg and 047.cfg for size 5. */
  public void test_047_AND_047_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 063.cfg and 003.cfg for size 5. */
  public void test_063_AND_003_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file java_names.cfg and 98_05_030.cfg for size
   * 5.
   */
  public void test_java_names_AND_98_05_030_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 005.cfg and 004.cfg for size 5. */
  public void test_005_AND_004_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file rna3.cfg and rna7.cfg for size 5. */
  public void test_rna3_AND_rna7_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file sml_patterns.cfg and 064.cfg for size 5. */
  public void test_sml_patterns_AND_064_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 008.cfg and 050.cfg for size 5. */
  public void test_008_AND_050_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 048.cfg and 006.cfg for size 5. */
  public void test_048_AND_006_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g4.cfg and 054.cfg for size 5. */
  public void test_g4_AND_054_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 034.cfg and 006.cfg for size 5. */
  public void test_034_AND_006_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 038.cfg and 030.cfg for size 5. */
  public void test_038_AND_030_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g5.cfg and 04_02_041.cfg for size 5. */
  public void test_g5_AND_04_02_041_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file 03_01_011.cfg and 03_01_011.cfg for size
   * 5.
   */
  public void test_03_01_011_AND_03_01_011_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file rna6.cfg and 063.cfg for size 5. */
  public void test_rna6_AND_063_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file 98_05_030.cfg and 05_03_114.cfg for size
   * 5.
   */
  public void test_98_05_030_AND_05_03_114_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file ada_calls.cfg and isocpp_qualid.cfg for
   * size 5.
   */
  public void test_ada_calls_AND_isocpp_qualid_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 025.cfg and 022.cfg for size 3. */
  public void test_025_AND_022_size3() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 025.cfg and 022.cfg for size 5. */
  public void test_025_AND_022_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 033.cfg and 98_05_030.cfg for size 5. */
  public void test_033_AND_98_05_030_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 021.cfg and g4.cfg for size 5. */
  public void test_021_AND_g4_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 026.cfg and 045.cfg for size 5. */
  public void test_026_AND_045_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 010.cfg and 062.cfg for size 5. */
  public void test_010_AND_062_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file java_modifiers.cfg and 018.cfg for size
   * 5.
   */
  public void test_java_modifiers_AND_018_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 062.cfg and 030.cfg for size 5. */
  public void test_062_AND_030_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 001.cfg and test.cfg for size 5. */
  public void test_001_AND_test_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 039.cfg and 049.cfg for size 5. */
  public void test_039_AND_049_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 025.cfg and 03_02_124.cfg for size 5. */
  public void test_025_AND_03_02_124_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file rna3.cfg and rna3.cfg for size 5. */
  public void test_rna3_AND_rna3_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 019.cfg and 038.cfg for size 5. */
  public void test_019_AND_038_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 001.cfg and 053.cfg for size 5. */
  public void test_001_AND_053_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file rna3.cfg and 03_05_170.cfg for size 5. */
  public void test_rna3_AND_03_05_170_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 042.cfg and 039.cfg for size 5. */
  public void test_042_AND_039_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 05_03_092.cfg and 050.cfg for size 5. */
  public void test_05_03_092_AND_050_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 022.cfg and 045.cfg for size 5. */
  public void test_022_AND_045_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 038.cfg and 05_06_028.cfg for size 5. */
  public void test_038_AND_05_06_028_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 011.cfg and 031.cfg for size 5. */
  public void test_011_AND_031_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 064.cfg and 017.cfg for size 5. */
  public void test_064_AND_017_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 031.cfg and 008.cfg for size 5. */
  public void test_031_AND_008_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g1.cfg and 05_03_114.cfg for size 5. */
  public void test_g1_AND_05_03_114_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g4.cfg and 053.cfg for size 5. */
  public void test_g4_AND_053_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 05_03_114.cfg and g4.cfg for size 5. */
  public void test_05_03_114_AND_g4_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file 06_10_036.cfg and 06_10_036.cfg for size
   * 5.
   */
  public void test_06_10_036_AND_06_10_036_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file arithmetic.cfg and g4.cfg for size 5. */
  public void test_arithmetic_AND_g4_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 038.cfg and 008.cfg for size 5. */
  public void test_038_AND_008_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 015.cfg and g2.cfg for size 5. */
  public void test_015_AND_g2_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 030.cfg and 047.cfg for size 5. */
  public void test_030_AND_047_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 049.cfg and 019.cfg for size 5. */
  public void test_049_AND_019_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 013.cfg and 045.cfg for size 5. */
  public void test_013_AND_045_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 019.cfg and g5.cfg for size 5. */
  public void test_019_AND_g5_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 039.cfg and 030.cfg for size 5. */
  public void test_039_AND_030_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 03_01_011.cfg and 020.cfg for size 5. */
  public void test_03_01_011_AND_020_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 042.cfg and 050.cfg for size 5. */
  public void test_042_AND_050_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 043.cfg and rna7.cfg for size 5. */
  public void test_043_AND_rna7_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 050.cfg and 039.cfg for size 5. */
  public void test_050_AND_039_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file sml_fvalbind.cfg and 91_08_014.cfg for
   * size 5.
   */
  public void test_sml_fvalbind_AND_91_08_014_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g4.cfg and 001.cfg for size 5. */
  public void test_g4_AND_001_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 027.cfg and 009.cfg for size 5. */
  public void test_027_AND_009_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file 05_03_114.cfg and 98_05_030.cfg for size
   * 5.
   */
  public void test_05_03_114_AND_98_05_030_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g4.cfg and 028.cfg for size 5. */
  public void test_g4_AND_028_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 025.cfg and 038.cfg for size 5. */
  public void test_025_AND_038_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 064.cfg and 048.cfg for size 5. */
  public void test_064_AND_048_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file rna6.cfg and rna7.cfg for size 5. */
  public void test_rna6_AND_rna7_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 03_09_027.cfg and 066.cfg for size 5. */
  public void test_03_09_027_AND_066_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 043.cfg and 043.cfg for size 5. */
  public void test_043_AND_043_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file java_casts.cfg and g4.cfg for size 5. */
  public void test_java_casts_AND_g4_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 063.cfg and 008.cfg for size 5. */
  public void test_063_AND_008_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 019.cfg and 91_08_014.cfg for size 5. */
  public void test_019_AND_91_08_014_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 014.cfg and 056.cfg for size 5. */
  public void test_014_AND_056_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file test.cfg and 05_03_114.cfg for size 5. */
  public void test_test_AND_05_03_114_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 010.cfg and 021.cfg for size 5. */
  public void test_010_AND_021_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 024.cfg and 020.cfg for size 5. */
  public void test_024_AND_020_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 051.cfg and 002.cfg for size 5. */
  public void test_051_AND_002_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g4.cfg and rna3.cfg for size 5. */
  public void test_g4_AND_rna3_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 047.cfg and 049.cfg for size 5. */
  public void test_047_AND_049_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 036.cfg and 051.cfg for size 5. */
  public void test_036_AND_051_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 014.cfg and 030.cfg for size 5. */
  public void test_014_AND_030_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 047.cfg and 079.cfg for size 5. */
  public void test_047_AND_079_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 013.cfg and 053.cfg for size 5. */
  public void test_013_AND_053_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 91_08_014.cfg and 039.cfg for size 5. */
  public void test_91_08_014_AND_039_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 039.cfg and 024.cfg for size 5. */
  public void test_039_AND_024_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 002.cfg and 034.cfg for size 5. */
  public void test_002_AND_034_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 049.cfg and 013.cfg for size 5. */
  public void test_049_AND_013_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 061.cfg and java_names.cfg for size 5. */
  public void test_061_AND_java_names_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 045.cfg and 001.cfg for size 5. */
  public void test_045_AND_001_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file isocpp_qualid.cfg and 032.cfg for size 5.
   */
  public void test_isocpp_qualid_AND_032_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 056.cfg and 038.cfg for size 5. */
  public void test_056_AND_038_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 050.cfg and 033.cfg for size 5. */
  public void test_050_AND_033_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 054.cfg and 013.cfg for size 5. */
  public void test_054_AND_013_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 009.cfg and 002.cfg for size 5. */
  public void test_009_AND_002_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 063.cfg and 013.cfg for size 5. */
  public void test_063_AND_013_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file pascal_typed.cfg and 025.cfg for size 5. */
  public void test_pascal_typed_AND_025_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 038.cfg and 014.cfg for size 5. */
  public void test_038_AND_014_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 053.cfg and 004.cfg for size 5. */
  public void test_053_AND_004_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 039.cfg and 013.cfg for size 5. */
  public void test_039_AND_013_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 013.cfg and 04_02_041.cfg for size 5. */
  public void test_013_AND_04_02_041_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 014.cfg and 063.cfg for size 5. */
  public void test_014_AND_063_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 048.cfg and ada_calls.cfg for size 5. */
  public void test_048_AND_ada_calls_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 025.cfg and 001.cfg for size 5. */
  public void test_025_AND_001_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 011.cfg and 91_08_014.cfg for size 5. */
  public void test_011_AND_91_08_014_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 013.cfg and 049.cfg for size 5. */
  public void test_013_AND_049_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 078.cfg and 018.cfg for size 5. */
  public void test_078_AND_018_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file 05_06_028.cfg and 05_06_028.cfg for size
   * 5.
   */
  public void test_05_06_028_AND_05_06_028_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 010.cfg and 034.cfg for size 5. */
  public void test_010_AND_034_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file 91_08_014.cfg and 91_08_014.cfg for size
   * 5.
   */
  public void test_91_08_014_AND_91_08_014_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 053.cfg and 042.cfg for size 5. */
  public void test_053_AND_042_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 026.cfg and 025.cfg for size 5. */
  public void test_026_AND_025_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 043.cfg and 032.cfg for size 5. */
  public void test_043_AND_032_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 039.cfg and 025.cfg for size 5. */
  public void test_039_AND_025_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file java_casts.cfg and java_casts.cfg for
   * size 5.
   */
  public void test_java_casts_AND_java_casts_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 030.cfg and 054.cfg for size 5. */
  public void test_030_AND_054_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 007.cfg and g2.cfg for size 5. */
  public void test_007_AND_g2_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 001.cfg and 056.cfg for size 5. */
  public void test_001_AND_056_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 03_01_011.cfg and 001.cfg for size 5. */
  public void test_03_01_011_AND_001_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 010.cfg and 014.cfg for size 5. */
  public void test_010_AND_014_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file java_modifiers.cfg and 91_08_014.cfg for
   * size 5.
   */
  public void test_java_modifiers_AND_91_08_014_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g4.cfg and 056.cfg for size 5. */
  public void test_g4_AND_056_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 04_02_041.cfg and 021.cfg for size 5. */
  public void test_04_02_041_AND_021_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 030.cfg and 039.cfg for size 5. */
  public void test_030_AND_039_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file test.cfg and 079.cfg for size 5. */
  public void test_test_AND_079_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 038.cfg and 039.cfg for size 5. */
  public void test_038_AND_039_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 019.cfg and 98_05_030.cfg for size 5. */
  public void test_019_AND_98_05_030_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 026.cfg and 049.cfg for size 5. */
  public void test_026_AND_049_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 024.cfg and 98_05_030.cfg for size 5. */
  public void test_024_AND_98_05_030_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 044.cfg and 053.cfg for size 5. */
  public void test_044_AND_053_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g7.cfg and 98_05_030.cfg for size 5. */
  public void test_g7_AND_98_05_030_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 001.cfg and 038.cfg for size 5. */
  public void test_001_AND_038_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file g4.cfg and 019.cfg for size 5. */
  public void test_g4_AND_019_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 022.cfg and 047.cfg for size 5. */
  public void test_022_AND_047_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 05_06_028.cfg and 066.cfg for size 5. */
  public void test_05_06_028_AND_066_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 013.cfg and 010.cfg for size 5. */
  public void test_013_AND_010_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 063.cfg and 03_01_011.cfg for size 5. */
  public void test_063_AND_03_01_011_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 054.cfg and 047.cfg for size 5. */
  public void test_054_AND_047_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 033.cfg and 023.cfg for size 5. */
  public void test_033_AND_023_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 054.cfg and 001.cfg for size 5. */
  public void test_054_AND_001_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 012.cfg and g3.cfg for size 5. */
  public void test_012_AND_g3_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 055.cfg and 055.cfg for size 5. */
  public void test_055_AND_055_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file java_arrays.cfg and 022.cfg for size 5. */
  public void test_java_arrays_AND_022_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 045.cfg and 013.cfg for size 5. */
  public void test_045_AND_013_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 002.cfg and 010.cfg for size 5. */
  public void test_002_AND_010_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file rna3.cfg and voss-light.cfg for size 5. */
  public void test_rna3_AND_voss_light_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 020.cfg and 98_08_215.cfg for size 5. */
  public void test_020_AND_98_08_215_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 039.cfg and 010.cfg for size 5. */
  public void test_039_AND_010_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 043.cfg and 039.cfg for size 5. */
  public void test_043_AND_039_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 026.cfg and 053.cfg for size 5. */
  public void test_026_AND_053_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 026.cfg and g3.cfg for size 5. */
  public void test_026_AND_g3_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 054.cfg and g3.cfg for size 5. */
  public void test_054_AND_g3_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 006.cfg and 079.cfg for size 5. */
  public void test_006_AND_079_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 044.cfg and 044.cfg for size 5. */
  public void test_044_AND_044_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file voss-light.cfg and 039.cfg for size 5. */
  public void test_voss_light_AND_039_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 056.cfg and g4.cfg for size 5. */
  public void test_056_AND_g4_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 007.cfg and ada_is.cfg for size 5. */
  public void test_007_AND_ada_is_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file rna7.cfg and voss-light.cfg for size 5. */
  public void test_rna7_AND_voss_light_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file test.cfg and 013.cfg for size 5. */
  public void test_test_AND_013_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file java_arrays.cfg and java_arrays.cfg for
   * size 5.
   */
  public void test_java_arrays_AND_java_arrays_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 03_01_011.cfg and rna7.cfg for size 5. */
  public void test_03_01_011_AND_rna7_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 062.cfg and 022.cfg for size 5. */
  public void test_062_AND_022_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 007.cfg and 079.cfg for size 5. */
  public void test_007_AND_079_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 030.cfg and 030.cfg for size 5. */
  public void test_030_AND_030_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 079.cfg and 06_10_036.cfg for size 5. */
  public void test_079_AND_06_10_036_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 001.cfg and 054.cfg for size 5. */
  public void test_001_AND_054_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 030.cfg and 051.cfg for size 5. */
  public void test_030_AND_051_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 050.cfg and 027.cfg for size 5. */
  public void test_050_AND_027_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 022.cfg and ada_calls.cfg for size 5. */
  public void test_022_AND_ada_calls_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 063.cfg and 021.cfg for size 5. */
  public void test_063_AND_021_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 042.cfg and rna7.cfg for size 5. */
  public void test_042_AND_rna7_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 030.cfg and 014.cfg for size 5. */
  public void test_030_AND_014_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 055.cfg and 010.cfg for size 5. */
  public void test_055_AND_010_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 044.cfg and 021.cfg for size 5. */
  public void test_044_AND_021_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file 03_02_124.cfg and 03_05_170.cfg for size
   * 5.
   */
  public void test_03_02_124_AND_03_05_170_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 010.cfg and 038.cfg for size 5. */
  public void test_010_AND_038_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 061.cfg and 048.cfg for size 5. */
  public void test_061_AND_048_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file ada_calls.cfg and ada_calls.cfg for size
   * 5.
   */
  public void test_ada_calls_AND_ada_calls_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 056.cfg and g2.cfg for size 5. */
  public void test_056_AND_g2_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 014.cfg and 045.cfg for size 5. */
  public void test_014_AND_045_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 007.cfg and 049.cfg for size 5. */
  public void test_007_AND_049_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 063.cfg and 014.cfg for size 5. */
  public void test_063_AND_014_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file rna3.cfg and 066.cfg for size 5. */
  public void test_rna3_AND_066_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 053.cfg and 056.cfg for size 5. */
  public void test_053_AND_056_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file 05_03_114.cfg and sml_fvalbind.cfg for
   * size 5.
   */
  public void test_05_03_114_AND_sml_fvalbind_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 053.cfg and 047.cfg for size 5. */
  public void test_053_AND_047_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 079.cfg and 043.cfg for size 5. */
  public void test_079_AND_043_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 063.cfg and 039.cfg for size 5. */
  public void test_063_AND_039_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 050.cfg and pascal_begin.cfg for size 5. */
  public void test_050_AND_pascal_begin_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 056.cfg and 053.cfg for size 5. */
  public void test_056_AND_053_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 045.cfg and g2.cfg for size 5. */
  public void test_045_AND_g2_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file rna7.cfg and rna3.cfg for size 5. */
  public void test_rna7_AND_rna3_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 003.cfg and 034.cfg for size 5. */
  public void test_003_AND_034_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /**
   * Intersection constraint from file arithmetic2.cfg and arithmetic.cfg for
   * size 5.
   */
  public void test_arithmetic2_AND_arithmetic_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 082.cfg and 05_03_114.cfg for size 5. */
  public void test_082_AND_05_03_114_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 053.cfg and 010.cfg for size 5. */
  public void test_053_AND_010_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 032.cfg and 038.cfg for size 5. */
  public void test_032_AND_038_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 049.cfg and 025.cfg for size 5. */
  public void test_049_AND_025_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 024.cfg and 009.cfg for size 5. */
  public void test_024_AND_009_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 047.cfg and 026.cfg for size 5. */
  public void test_047_AND_026_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 005.cfg and 045.cfg for size 5. */
  public void test_005_AND_045_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 014.cfg and 014.cfg for size 5. */
  public void test_014_AND_014_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file sml_fvalbind.cfg and 010.cfg for size 5. */
  public void test_sml_fvalbind_AND_010_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 063.cfg and 022.cfg for size 5. */
  public void test_063_AND_022_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 078.cfg and 014.cfg for size 5. */
  public void test_078_AND_014_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 044.cfg and 030.cfg for size 5. */
  public void test_044_AND_030_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 011.cfg and 021.cfg for size 5. */
  public void test_011_AND_021_size5() throws Exception{
    doTest(false, Double.MAX_VALUE);
  }

  /** Intersection constraint from file 001.cfg and 039.cfg for size 5. */
  public void test_001_AND_039_size5() throws Exception{
    doTest(true, Double.MAX_VALUE);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_arithmetic() throws Exception{
    doTest(true, 333);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_04_02_041() throws Exception{
    doTest(false, 305.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_044() throws Exception{
    doTest(true, 312.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_008() throws Exception{
    doTest(true, 289);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_024() throws Exception{
    doTest(true, 913);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_020() throws Exception{
    doTest(false, 251);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_g2() throws Exception{
    doTest(false, 257);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_012() throws Exception{
    doTest(false, 256.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_011() throws Exception{
    doTest(true, 280.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_056() throws Exception{
    doTest(true, 281.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_arithmetic2() throws Exception{
    doTest(true, 315);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_033() throws Exception{
    doTest(false, 269.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_028() throws Exception{
    doTest(true, 283);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_03_05_170() throws Exception{
    doTest(true, 283);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_019() throws Exception{
    doTest(true, 281.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_042() throws Exception{
    doTest(true, 300.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_001() throws Exception{
    doTest(true, 293.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_054() throws Exception{
    doTest(true, 276.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_017() throws Exception{
    doTest(true, 282.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_049() throws Exception{
    doTest(true, 320);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_03_01_011() throws Exception{
    doTest(true, 303);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_g1() throws Exception{
    doTest(true, 284);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_006() throws Exception{
    doTest(true, 311.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 40.
   */
  public void test_cfg_006_size40() throws Exception{
    doTest(true, 0);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_g7() throws Exception{
    doTest(false, 257.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_061() throws Exception{
    doTest(false, 257.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_007() throws Exception{
    doTest(true, 305.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_05_06_028() throws Exception{
    doTest(true, 286.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_91_08_014() throws Exception{
    doTest(true, 310.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_066() throws Exception{
    doTest(false, 271.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_022() throws Exception{
    doTest(true, 284.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_voss_light() throws Exception{
    doTest(true, 302.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 38.
   */
  public void test_cfg_voss_light_38() throws Exception{
    doTest(true, 0);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_082() throws Exception{
    doTest(true, 287);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_038() throws Exception{
    doTest(true, 284.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_079() throws Exception{
    doTest(false, 255.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_ada_calls() throws Exception{
    doTest(true, 334.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_98_08_215() throws Exception{
    doTest(false, 240.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_045() throws Exception{
    doTest(true, 285.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_055() throws Exception{
    doTest(true, 286);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_036() throws Exception{
    doTest(true, 306.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_010() throws Exception{
    doTest(true, 287.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_test() throws Exception{
    doTest(false, 253.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_05_03_114() throws Exception{
    doTest(true, 304);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_rna6() throws Exception{
    doTest(true, 296.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_029() throws Exception{
    doTest(true, 296);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_043() throws Exception{
    doTest(true, 277.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_005() throws Exception{
    doTest(false, 253.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_047() throws Exception{
    doTest(true, 302.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_rna7() throws Exception{
    doTest(true, 293);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_018() throws Exception{
    doTest(true, 294.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_015() throws Exception{
    doTest(false, 244.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_pascal_begin() throws Exception{
    doTest(true, 302.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_053() throws Exception{
    doTest(true, 286.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_014() throws Exception{
    doTest(true, 308.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_ada_is() throws Exception{
    doTest(false, 831);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_064() throws Exception{
    doTest(false, 256);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_052() throws Exception{
    doTest(false, 242.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_030() throws Exception{
    doTest(true, 284.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_051() throws Exception{
    doTest(true, 308.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_078() throws Exception{
    doTest(false, 248.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_025() throws Exception{
    doTest(true, 293.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_06_10_036() throws Exception{
    doTest(true, 321);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_034() throws Exception{
    doTest(true, 288.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_063() throws Exception{
    doTest(true, 296.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_048() throws Exception{
    doTest(true, 298);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_98_05_030() throws Exception{
    doTest(true, 343.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_003() throws Exception{
    doTest(true, 304);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_03_02_124() throws Exception{
    doTest(false, 298.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_013() throws Exception{
    doTest(true, 308.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_009() throws Exception{
    doTest(false, 292);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_004() throws Exception{
    doTest(false, 250.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_021() throws Exception{
    doTest(true, 286.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_g5() throws Exception{
    doTest(true, 299.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_03_09_081() throws Exception{
    doTest(true, 279);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_java_names() throws Exception{
    doTest(true, 314.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_002() throws Exception{
    doTest(true, 286.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_039() throws Exception{
    doTest(true, 295);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_rna3() throws Exception{
    doTest(true, 282);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_pascal_typed() throws Exception{
    doTest(true, 295.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_sml_patterns() throws Exception{
    doTest(true, 302.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_isocpp_qualid() throws Exception{
    doTest(true, 280.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_java_modifiers() throws Exception{
    doTest(false, 255.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_05_03_092() throws Exception{
    doTest(true, 298.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_027() throws Exception{
    doTest(true, 298.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_java_casts() throws Exception{
    doTest(false, 250.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_sml_fvalbind() throws Exception{
    doTest(true, 312);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_023() throws Exception{
    doTest(true, 295);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_031() throws Exception{
    doTest(true, 299.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_050() throws Exception{
    doTest(true, 295.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_084() throws Exception{
    doTest(false, 245.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_java_arrays() throws Exception{
    doTest(true, 294.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_062() throws Exception{
    doTest(true, 286.67);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_g3() throws Exception{
    doTest(true, 286);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_032() throws Exception{
    doTest(false, 301.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_026() throws Exception{
    doTest(true, 287);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_03_09_027() throws Exception{
    doTest(false, 287.33);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 7.
   */
  public void test_cfg_g4() throws Exception{
    doTest(true, 334);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_001_20() throws Exception{
    doTest(true, 3000);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_010_20() throws Exception{
    doTest(true, 4000);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_012_20() throws Exception{
    doTest(true, 609);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_013_20() throws Exception{
    doTest(true, 6000);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_014_20() throws Exception{
    doTest(true, 5400);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_021_20() throws Exception{
    doTest(true, 612);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_022_20() throws Exception{
    doTest(true, 34000);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_027_20() throws Exception{
    doTest(true, 3000);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_030_20() throws Exception{
    doTest(true, 3000);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_038_10() throws Exception{
    doTest(true, 653);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_049_20() throws Exception{
    doTest(true, 2378);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_05_06_028_20() throws Exception{
    doTest(true, 1600);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_063_20() throws Exception{
    doTest(true, 5000);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_arithmetic_20() throws Exception{
    doTest(true, 4000);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_g1_20() throws Exception{
    doTest(true, 790);
  }

  /**
   * Test created by converting a CFGAnalyzer example to hampi grammar
   * membership constraint for size 20.
   */
  public void test_cfg_rna6_20() throws Exception{
    doTest(true, 900);
  }

}
