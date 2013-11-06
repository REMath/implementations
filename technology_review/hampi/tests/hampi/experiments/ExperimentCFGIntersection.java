package hampi.experiments;

import static hampi.experiments.HampiExperiments.*;
import hampi.utils.*;

import java.io.*;
import java.util.*;

/**
 * This runs the experiment in which we analyze CFGs for intersection emptiness.
 * The intersection is undecidable in general but solvable when bounded.
 */
public final class ExperimentCFGIntersection{

  /**
   * arguments: low high inputFile
   */
  public static void main(String[] args) throws Exception{
    if (args.length != 4){
      printUsage();
      System.exit(1);
    }
    int low = Integer.parseInt(args[0]);
    int high = Integer.parseInt(args[1]);
    List<List<String>> fileLists = listPerLine(args[2]);
    File outputDir = new File(args[3]);
    if (!argsOK(low, high, outputDir)){
      printUsage();
      System.exit(1);
    }
    if (!outputDir.exists()){//create dir if needed
      outputDir.mkdirs();
    }

    //duplicate all output to log 
    System.setErr(System.out);
    File logFile = new File(outputDir, "intersection_log.txt");
    System.setOut(new PrintStream(Files.tee(System.out, new FileOutputStream(logFile))));
    System.out.println(new Date() + " start");
    System.out.println("Logging to " + logFile.getAbsolutePath());
    System.out.println("arguments: " + CollectionsExt.join(" ", args));
    runIntersectionExperiment(low, high, fileLists, outputDir);
    System.out.println(new Date() + " finished");
  }

  private static void runIntersectionExperiment(int low, int high, List<List<String>> fileLists, File outputDir) throws Exception{
    //Note: lift the size loop so we can create the svg file one each iteration and not just at the very end
    SolverExperimentResultSet<Pair<Boolean, Double>> hampiResults = new SolverExperimentResultSet<Pair<Boolean, Double>>("hampi");
    SolverExperimentResultSet<Pair<Boolean, Double>> cfgResults = new SolverExperimentResultSet<Pair<Boolean, Double>>("cfg");
    String experimentName = "intersection";
    for (int size = low; size <= high; size++){
      System.out.println("---------------------------------------------------------");
      System.out.println("size " + size);

      runHampiIntersection(hampiResults, size, fileLists);
      runOnCFGFilePairs(cfgResults, "-n", size, fileLists);
      Set<String> inconsistencies = inconsistencies(size, cfgResults, hampiResults);
      if (!inconsistencies.isEmpty()){
        File inconsitenciesFile = new File(outputDir, experimentName + "_inconsistencies.txt");
        Files.writeToFile("size " + size + " " + inconsistencies + "\n", inconsitenciesFile, true);
      }
      SolverExperimentResultSet<Double> timeRatio = SolverExperimentResultSet.timeRatio(cfgResults, hampiResults, 0);
      createResultGraphs(hampiResults, cfgResults, experimentName, timeRatio, outputDir);
      printInRatioOrder(size, timeRatio);
    }
  }

  private static void runOnCFGFilePairs(SolverExperimentResultSet<Pair<Boolean, Double>> results, String option, int size, List<List<String>> fileNameLists){
    for (List<String> pair : fileNameLists){
      String fname1 = pair.get(0);
      String fname2 = pair.get(1);
      if (skipFile(fname1) || skipFile(fname2)){
        continue;
      }
      File f1 = new File(fname1);
      File f2 = new File(fname2);

      Pair<Boolean, Double> p = CFGAnalyzer.run(size, null, option, f1, f2);
      System.out.println("cfg " + f1.getName() + "_AND_" + f2.getName() + p);
      results.addResult(f1.getName() + "_AND_" + f2.getName(), size, p);
    }
  }

  private static void runHampiIntersection(SolverExperimentResultSet<Pair<Boolean, Double>> results, int size, List<List<String>> cfgFileNameLists) throws IOException{
    for (List<String> pair : cfgFileNameLists){
      String fname1 = pair.get(0);
      String fname2 = pair.get(1);
      if (skipFile(fname1) || skipFile(fname2)){
        continue;
      }
      File f1 = new File(fname1);
      File f2 = new File(fname2);

      String hampiConstraint = CFG2HMP.convertToIntersectionConstraint(size, f1.getAbsolutePath(), f2.getAbsolutePath());
      Pair<Boolean, Double> p = solveConstraint(hampiConstraint, null);
      System.out.println("hampi " + f1.getName() + "_AND_" + f2.getName() + p);
      results.addResult(f1.getName() + "_AND_" + f2.getName(), size, p);
    }
  }

  private static boolean argsOK(int low, int high, File outputDir){
    if (low < 0 || low > high)
      return false;
    if (outputDir.exists() && !outputDir.isDirectory())
      return false;
    return true;
  }

  private static void printUsage(){
    System.out.println("Usage " + ExperimentCFGIntersection.class.getSimpleName() + " low high inputFile outputDir");
    System.out.println("where ");
    System.out.println("  'low' is the shortest solution string to try");
    System.out.println("  'high' is the longest solution string to try");
    System.out.println("  'inputFile' is the name of the file with the grammars (in CFG format)");
    System.out.println("  'outputDir' is the name of the directory to place the output and the log (optional, default is the current directory)");
  }

}
