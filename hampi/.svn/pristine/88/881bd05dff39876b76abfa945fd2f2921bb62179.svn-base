package hampi.experiments;

import static hampi.experiments.HampiExperiments.*;
import hampi.utils.*;

import java.io.*;
import java.util.*;

/**
 * This runs the emptiness experiment which compares the performance of hampi
 * and CFG analyzer on checking grammar emptiness.
 */
public final class ExperimentCFGEmptiness{

  public static void main(String[] args) throws Exception{
    //check arguments
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
    if (!outputDir.exists()){//make the dir if needed
      outputDir.mkdirs();
    }

    //duplicate all output to log
    System.setErr(System.out);
    File logFile = new File(outputDir, "emptiness_log.txt");
    System.setOut(new PrintStream(Files.tee(System.out, new FileOutputStream(logFile))));
    System.out.println(new Date() + " start");
    System.out.println("Logging to " + logFile.getAbsolutePath());
    System.out.println("arguments: " + CollectionsExt.join(" ", args));
    runEmptinessExperiment(low, high, fileLists, outputDir);
    System.out.println(new Date() + " finished");
  }

  public static void runEmptinessExperiment(int low, int high, List<List<String>> fileLists, File outputDir) throws Exception{
    SolverExperimentResultSet<Pair<Boolean, Double>> hampiResults = new SolverExperimentResultSet<Pair<Boolean, Double>>("hampi");
    SolverExperimentResultSet<Pair<Boolean, Double>> cfgResults = new SolverExperimentResultSet<Pair<Boolean, Double>>("cfganalyzer");
    String experimentName = "emptiness";
    for (int size = low; size <= high; size++){
      System.out.println("---------------------------------------------------------");
      System.out.println("size " + size);
      runHampiEmptinessOnCFGFiles(fileLists, hampiResults, size);
      runOnCFGFiles(fileLists, cfgResults, size);
      Set<String> inconsistencies = inconsistencies(size, cfgResults, hampiResults);
      if (!inconsistencies.isEmpty()){
        File inconsitenciesFile = new File(outputDir, experimentName + "_inconsistencies.txt");
        Files.writeToFile("size " + size + " " + inconsistencies + "\n", inconsitenciesFile, true);
      }
      SolverExperimentResultSet<Double> timeRatio = SolverExperimentResultSet.timeRatio(cfgResults, hampiResults, 0);
      createResultGraphs(hampiResults, cfgResults, experimentName, timeRatio, outputDir);
      System.out.println();
      printInRatioOrder(size, timeRatio);
    }
  }

  private static void runOnCFGFiles(List<List<String>> fileLists, SolverExperimentResultSet<Pair<Boolean, Double>> results, int size) throws Exception{
    System.out.println("cfg: " + size);
    for (List<String> flist : fileLists){
      String fname = flist.get(0);
      if (skipFile(fname)){
        continue;
      }
      File cfgAnalyzerFile = new File(fname);
      Pair<Boolean, Double> p = CFGAnalyzer.run(size, null, "-e", cfgAnalyzerFile);
      results.addResult(cfgAnalyzerFile.getName(), size, p);
      System.out.println("cfg " + cfgAnalyzerFile.getName() + p);
    }
  }

  private static void runHampiEmptinessOnCFGFiles(List<List<String>> fileLists, SolverExperimentResultSet<Pair<Boolean, Double>> results, int size) throws Exception{
    System.out.println("hampi: " + size);
    for (List<String> flist : fileLists){
      String fname = flist.get(0);
      if (skipFile(fname)){
        continue;
      }
      File cfgAnalyzerFile = new File(fname);

      String format = CFG2HMP.convertToEmptinessConstraint(size, cfgAnalyzerFile.getAbsolutePath());
      StringBuilder sb = new StringBuilder();
      Pair<Boolean, Double> p = solveConstraint(format, sb);
      System.out.println(sb);
      results.addResult(cfgAnalyzerFile.getName(), size, p);
      System.out.println("hampi " + cfgAnalyzerFile.getName() + p);
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
    System.out.println("Usage ExperimentCFGEmptiness low high inputFile outputDir");
    System.out.println("where ");
    System.out.println("  'low' is the shortest solution string to try");
    System.out.println("  'high' is the longest solution string to try");
    System.out.println("  'inputFile' is the file with the grammars (in CFG format)");
    System.out.println("  'outputDir' is the output directory for the results");
  }
}
