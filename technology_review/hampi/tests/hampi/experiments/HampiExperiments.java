package hampi.experiments;

import hampi.*;
import hampi.utils.*;

import java.io.*;
import java.util.*;

import org.antlr.runtime.RecognitionException;

/**
 * Collection of options and code common to Hampi experiments.
 */
public final class HampiExperiments{

  private HampiExperiments(){
    throw new IllegalStateException("do not instantiate");
  }

  /**
   * For these files, Hampi chokes. Either crashes or spins forever.
   */
  public static final List<String> HAMPI_CFG_BUGS;

  /**
   * These grammars use mutli-character terminals, and the semantics differ from
   * Hampi to CFGAnalyser. So we skip them in comparisons.
   */
  public static final List<String> MULTI_CHAR_TERMINALS;
  /**
   * On these grammars, Hampi is very slow (compared to CFGAnalyzer), at size 25
   * or more.
   */
  public static final List<String> HAMPI_VERY_SLOW;

  static{
    try{
      HAMPI_CFG_BUGS = Files.readWhole("tests/hampi/experiments/hampi_bugs.txt");
      MULTI_CHAR_TERMINALS = Files.readWhole("tests/hampi/experiments/multi_char_grammars.txt");
      HAMPI_VERY_SLOW = Files.readWhole("tests/hampi/experiments/hampi_slow.txt");
    }catch (IOException e){
      throw new HampiException(e);
    }
  }

  public static final int REPEAT = 1;//we repeat every run this many times and report averages

  /**
   * Solves the Hampi constraint and returns the result (sat/unsat and time).
   * The Hampi output is passed to out.
   */
  public static Pair<Boolean, Double> solveConstraint(String hampiConstraint, StringBuilder out) throws IOException{
    File tmp = File.createTempFile("tmp", ".hmp");
    Files.writeToFile(hampiConstraint, tmp);

    try{
      long[] times = new long[REPEAT];
      boolean isSat = false;
      for (int rep = 1; rep <= REPEAT; rep++){
        ByteArrayOutputStream os = new ByteArrayOutputStream();
        StopWatch w = new StopWatch("");
        w.start();
        int exec = Command.exec(new String[] { "/bin/bash", "hampi_client.sh", "4444", tmp.getAbsolutePath() }, new PrintStream(os));
        w.stop();
        if (out != null && rep == REPEAT){
          out.append(os.toString());
        }

        isSat = !(os.toString().contains("UNSAT")) && !(os.toString().contains("refused"));
        times[rep - 1] = w.getTotal();
      }

      return Pair.create(isSat, CollectionsExt.mean(times));
    }finally{
      tmp.delete();
    }
  }

  //XXX Solves the constraint in the same JVM
  public static Pair<Boolean, Double> solveConstraint2(String hampiConstraint, StringBuilder out) throws IOException{
    long[] times = new long[REPEAT];
    boolean isSat = false;
    for (int rep = 1; rep <= REPEAT; rep++){
      ByteArrayOutputStream os = new ByteArrayOutputStream();
      StopWatch w = new StopWatch("");
      w.start();
      try{
        InputStream istream = new ByteArrayInputStream(hampiConstraint.getBytes());
        Hampi.run(false, false, istream);
        isSat = true;
      }catch (HampiResultException e){
        isSat = false;
      }catch (RecognitionException e){
        throw new IllegalStateException(e);
      }
      w.stop();
      if (out != null && rep == REPEAT){
        out.append(os.toString());
      }
      times[rep - 1] = w.getTotal();
    }

    return Pair.create(isSat, CollectionsExt.mean(times));
  }

  /**
   * Creates 3 SVG graphs - one for Hampi results, one for cfganalyzer results,
   * one for ratio. Also creates a HTML page with all 3 graphs.
   */
  public static void createResultGraphs(SolverExperimentResultSet<Pair<Boolean, Double>> hampiResults, SolverExperimentResultSet<Pair<Boolean, Double>> cfgResults, String experimentName,
      SolverExperimentResultSet<Double> timeRatio, File outputDir) throws IOException{

    StringBuilder html = new StringBuilder();
    html.append("<html><body>");

    if (timeRatio.experimentCount() > 0){
      String expName = experimentName + "_ratio";
      //draw the ratio graph
      String ylabel = "ratio (times)";
      String dataFileContent = timeRatio.asGNUPlotDataFileContent(SolverExperimentResultSet.DOUBLE_FORMATTER);
      File dataFile = Files.writeToFile(dataFileContent, gplotDataFile(expName, outputDir));
      String gnuplotFileContent = timeRatio.asGNUPlotFileContent(outputDir, dataFile.getName(), expName, ylabel, false);
      File gplotFile = Files.writeToFile(gnuplotFileContent, gplotFile(expName, outputDir));
      GNUPlot.runGNUplot(gplotFile);
      html.append(svgImage(expName));

      //draw the ratio graph averaged
      expName = experimentName + "_ratio_avg";
      SolverExperimentResultSet<Pair<Double, Double>> averageRatios = SolverExperimentResultSet.averageOfDoubles(timeRatio);
      String avgRatiosData = averageRatios.asGNUPlotDataFileContent(SolverExperimentResultSet.DOUBLE_DOUBLE_FORMATTER);
      File avgDataFile = Files.writeToFile(avgRatiosData, gplotDataFile(expName, outputDir));
      String avgRatiosGnuplot = averageRatios.asGNUPlotFileContentWithErrorbars(outputDir, avgDataFile.getName(), expName, ylabel);
      File avgGplotFile = Files.writeToFile(avgRatiosGnuplot, gplotFile(expName, outputDir));
      GNUPlot.runGNUplot(avgGplotFile);
      html.append(svgImage(expName));

      html.append("<br>\n");
    }
    if (cfgResults.experimentCount() > 0){
      String expName = experimentName + "_cfg";

      //draw the cfg time graph
      String ylabel = "time (ms)";
      String dataFileContentCFG = cfgResults.asGNUPlotDataFileContent(SolverExperimentResultSet.BOOLEAN_DOUBLE_FORMATTER);
      File dataFileCFG = Files.writeToFile(dataFileContentCFG, gplotDataFile(expName, outputDir));
      String satFileContentCFG = cfgResults.asSatFileContent();
      Files.writeToFile(satFileContentCFG, satFile(expName, outputDir));
      String gnuplotFileContentCFG = cfgResults.asGNUPlotFileContent(outputDir, dataFileCFG.getName(), expName, ylabel, false);
      File gplotFileCFG = Files.writeToFile(gnuplotFileContentCFG, gplotFile(expName, outputDir));
      GNUPlot.runGNUplot(gplotFileCFG);
      html.append(svgImage(expName));

      //draw the cfg graph averaged
      expName = experimentName + "_cfg_avg";
      SolverExperimentResultSet<Pair<Double, Double>> averageCFGResults = SolverExperimentResultSet.averageOfPairs(cfgResults);
      String avgCfgData = averageCFGResults.asGNUPlotDataFileContent(SolverExperimentResultSet.DOUBLE_DOUBLE_FORMATTER);
      File avgDataFile = Files.writeToFile(avgCfgData, gplotDataFile(expName, outputDir));
      String avgCfgGnuplot = averageCFGResults.asGNUPlotFileContentWithErrorbars(outputDir, avgDataFile.getName(), expName, ylabel);
      File avgCfgGplotFile = Files.writeToFile(avgCfgGnuplot, gplotFile(expName, outputDir));
      GNUPlot.runGNUplot(avgCfgGplotFile);
      html.append(svgImage(expName));

      html.append("<br>\n");
    }
    if (hampiResults.experimentCount() > 0){
      //draw the hampi time graph
      String expName = experimentName + "_hmp";
      String ylabel = "time (ms)";
      String dataFileContentHMP = hampiResults.asGNUPlotDataFileContent(SolverExperimentResultSet.BOOLEAN_DOUBLE_FORMATTER);
      File dataFileHMP = Files.writeToFile(dataFileContentHMP, gplotDataFile(expName, outputDir));
      String satFileContentHMP = hampiResults.asSatFileContent();
      Files.writeToFile(satFileContentHMP, satFile(expName, outputDir));
      String gnuplotFileContentHMP = hampiResults.asGNUPlotFileContent(outputDir, dataFileHMP.getName(), expName, ylabel, false);
      File gplotFileHMP = Files.writeToFile(gnuplotFileContentHMP, gplotFile(expName, outputDir));
      GNUPlot.runGNUplot(gplotFileHMP);
      html.append(svgImage(expName));

      //draw the hampi graph averaged
      expName = experimentName + "_hmp_avg";
      SolverExperimentResultSet<Pair<Double, Double>> averageHampi = SolverExperimentResultSet.averageOfPairs(hampiResults);
      String avgHmpData = averageHampi.asGNUPlotDataFileContent(SolverExperimentResultSet.DOUBLE_DOUBLE_FORMATTER);
      File avgHmpDataFile = Files.writeToFile(avgHmpData, gplotDataFile(expName, outputDir));
      String avgHmpGnuplot = averageHampi.asGNUPlotFileContentWithErrorbars(outputDir, avgHmpDataFile.getName(), expName, ylabel);
      File avgHmpGplotFile = Files.writeToFile(avgHmpGnuplot, gplotFile(expName, outputDir));
      GNUPlot.runGNUplot(avgHmpGplotFile);
      html.append(svgImage(expName));

      html.append("<br>\n");
    }

    if (cfgResults.experimentCount() > 0 && hampiResults.experimentCount() > 0){
      String ylabel = "time (ms)";
      SolverExperimentResultSet<Pair<Double, Double>> averageCFGResults = SolverExperimentResultSet.averageOfPairs(cfgResults);
      SolverExperimentResultSet<Pair<Double, Double>> averageHampi = SolverExperimentResultSet.averageOfPairs(hampiResults);

      SolverExperimentResultSet<Pair<Double, Double>> averages = averageCFGResults.merge(averageHampi);
      String expName = experimentName + "_merge_avg";
      String avgMergeData = averages.asGNUPlotDataFileContent(SolverExperimentResultSet.DOUBLE_DOUBLE_FORMATTER);
      File avgMergeDataFile = Files.writeToFile(avgMergeData, gplotDataFile(expName, outputDir));
      String avgMergeGnuplot = averages.asGNUPlotFileContentWithErrorbars(outputDir, avgMergeDataFile.getName(), expName, ylabel);
      File avgMergeGplotFile = Files.writeToFile(avgMergeGnuplot, gplotFile(expName, outputDir));
      GNUPlot.runGNUplot(avgMergeGplotFile);
      html.append(svgImage(expName));

      html.append("<br>\n");
    }

    //create a html file with the graphs
    html.append("</body></html>");
    Files.writeToFile(html.toString(), new File(outputDir, experimentName + ".html"));
  }

  private static File satFile(String expName, File outputDir){
    return new File(outputDir, expName + "_sat.txt");
  }

  private static File gplotDataFile(String experimentName, File outputDir){
    return new File(outputDir, experimentName + ".data");
  }

  private static File gplotFile(String experimentName, File outputDir){
    return new File(outputDir, experimentName + ".gplot");
  }

  //embed SVG graph
  private static String svgImage(String fname){
    String height = "300px";
    String width = "300px";
    return "<object data=\"" + fname + ".svg\" type=\"image/svg+xml\" width=\"" + width + "\" height=\"" + height + "\"></object>";
  }

  /**
   * Prints the ratios for the given size, in the order of the time ratios.
   */
  public static void printInRatioOrder(int size, SolverExperimentResultSet<Double> timeRatio){
    System.out.println("Time ratios for size " + size);
    if (timeRatio.isEmpty())
      return;
    //print the worst cases for Hampi
    List<Pair<String, Integer>> sortedByTime = timeRatio.getPairsInOrder(new Comparator<Double>(){
      @Override
      public int compare(Double o1, Double o2){
        return o2.compareTo(o1);
      }
    });
    Set<String> reported = new LinkedHashSet<String>();
    for (Pair<String, Integer> pair : sortedByTime){
      if (pair.second == size && !reported.contains(pair.first)){
        System.out.println(pair.first + " -> " + timeRatio.getResult(pair.first, pair.second));
      }
      if (pair.second == size){
        reported.add(pair.first);
      }
    }
  }

  /**
   * Finds SAT/UNSAT inconsistencies between two sets of results.
   */
  public static Set<String> inconsistencies(int size, SolverExperimentResultSet<Pair<Boolean, Double>> r1, SolverExperimentResultSet<Pair<Boolean, Double>> r2){
    Set<String> incon = new LinkedHashSet<String>();
    for (String exp : r1.getExperimentNames()){
      Pair<Boolean, Double> p1 = r1.getResult(exp, size);
      Pair<Boolean, Double> p2 = r2.getResult(exp, size);
      assert p1 != null : r1.getName() + " " + exp;
      assert p2 != null : r2.getName() + " " + exp;
      boolean sat1 = p1.first;
      boolean sat2 = p2.first;
      if (sat1 != sat2){
        incon.add(exp);
      }
    }
    return incon;
  }

  /**
   * Reads the list of file name lists from a file. Each list is read from 1
   * line and names are separated by spaces.
   */
  public static List<List<String>> listPerLine(String fileName) throws IOException{
    File inputFile = new File(fileName);
    assert inputFile.isFile() : fileName + " must be a file";
    List<String> lines = Files.readWhole(inputFile);
    List<List<String>> res = new ArrayList<List<String>>(lines.size());
    for (String string : lines){
      res.add(Arrays.asList(string.split(" ")));
    }
    return res;
  }

  /* should we skip this file? */
  public static boolean skipFile(String fname){
    return HAMPI_CFG_BUGS.contains(fname) || MULTI_CHAR_TERMINALS.contains(fname) || HAMPI_VERY_SLOW.contains(fname);
  }

}
