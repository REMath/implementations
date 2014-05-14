package hampi.experiments;

import hampi.utils.*;

import java.io.*;
import java.util.*;

public class ExperimentWSU{
  private static final String WSU_TEMPLATE_MARKER = "$HAMPI_LENGTH$";
  private static final String WSU_TEMPLATES_DIR = "tests/hampi/experiments/resources/wsu";

  public static void main(String[] args) throws IOException{
    if (args.length != 3){
      printUsage();
      System.exit(1);
    }
    int low = Integer.parseInt(args[0]);
    int high = Integer.parseInt(args[1]);

    File outputDir = new File(args[2]);
    assert high >= 1 : "invalid value " + high;
    if (!argsOK(low, high, outputDir)){
      printUsage();
      System.exit(1);
    }
    if (!outputDir.exists()){
      outputDir.mkdirs();
    }

    //duplicate all output to log
    System.setErr(System.out);
    File logFile = new File(outputDir, "wsu_log.txt");
    System.setOut(new PrintStream(Files.tee(System.out, new FileOutputStream(logFile))));
    System.out.println(new Date() + " start");
    System.out.println("arguments: " + CollectionsExt.join(" ", args));
    System.out.println("Logging to " + logFile.getAbsolutePath());
    runWSUExperiment(low, high, outputDir);
    System.out.println(new Date() + " finished");
  }

  private static void printUsage(){
    System.out.println("Usage: ExperimentWSU low high outputDir");
    System.out.println("  'low' is the shortest solution string to try");
    System.out.println("  'high' is the longest solution string to try");
    System.out.println("  'outputDir' is the name of the directory to place the output and the log");
  }

  private static void runWSUExperiment(int low, int high, File outputDir) throws IOException{
    SolverExperimentResultSet<Pair<Boolean, Double>> hampiResults = new SolverExperimentResultSet<Pair<Boolean, Double>>("hampi");
    SolverExperimentResultSet<Pair<Boolean, Double>> cfgResults = new SolverExperimentResultSet<Pair<Boolean, Double>>("cfganalyzer");
    for (int i = low; i <= high; i++){
      runHampi(i, hampiResults);
      //CFG are empty

      SolverExperimentResultSet<Double> timeRatio = new SolverExperimentResultSet<Double>("ratio");
      HampiExperiments.createResultGraphs(hampiResults, cfgResults, "wsu", timeRatio, outputDir);
    }
  }

  /**
   * Runs the Hampi solver to find attacks with variable of length n.
   */
  private static void runHampi(int n, SolverExperimentResultSet<Pair<Boolean, Double>> hampiResults) throws IOException{
    System.out.println("size " + n);
    for (File queryFile : queryFilesSortedByName()){
        String constraint = instantiateTemplate(n, Files.getFileContents(queryFile));
      //        System.out.println(constraint);
              StringBuilder out = new StringBuilder();
      System.out.print("hampi " + n + " " + queryFile.getName() + " ");
      Pair<Boolean, Double> solveConstraint = HampiExperiments.solveConstraint(constraint, out);
      hampiResults.addResult(queryFile.getName(), n, solveConstraint);
      System.out.println(solveConstraint);
    }
  }

  public static File[] queryFilesSortedByName(){
    File[] listFiles = new File(WSU_TEMPLATES_DIR).listFiles(new FilenameFilter(){
      @Override
      public boolean accept(File dir, String name){
        return name.contains(".hmp.tmp");
      }
    });
    Arrays.sort(listFiles);//sort by name
    return listFiles;
  }

  public static String instantiateTemplate(int n, String fileContents){
    return fileContents.replace(WSU_TEMPLATE_MARKER, String.valueOf(n));
  }

  private static boolean argsOK(int low, int high, File outputDir){
    if (low < 0 || low > high)
      return false;
    if (outputDir.exists() && !outputDir.isDirectory())
      return false;
    return true;
  }
}