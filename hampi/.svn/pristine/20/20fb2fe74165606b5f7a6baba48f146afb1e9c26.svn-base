package hampi.experiments;

import hampi.parser.*;
import hampi.utils.*;

import java.io.*;
import java.util.*;

import org.antlr.runtime.RecognitionException;

/**
 * Analyzes data collected in the WSU experiments and creates plots.
 */
public class ExperimentWSUAnalyze{
  private static final String DATA_FILE = "wsu_hmp.data";
  private static final String SAT_FILE = "results_WSU_fixed/wsu_hmp_sat.txt";

  public static void main(String[] args) throws IOException,RecognitionException{

    File[] queryFilesSortedByName = ExperimentWSU.queryFilesSortedByName();
    boolean[] satisfiable = findSatisfiableQueries(queryFilesSortedByName);

    BigTable satTable = BigTable.readFromFile(SAT_FILE);

    //check that we do not claim something is SAT when it's not
    checkSatisfiableQueries(queryFilesSortedByName, satisfiable, satTable);

    //for each size count how many sat
    printRatioOfSATperN(satisfiable, satTable);

        plotGrammarSizeVsTime(queryFilesSortedByName, satisfiable);

    //    plotTimeVsPercentOfSolvableQueries(queryFilesSortedByName);
  }

  private static void plotTimeVsPercentOfSolvableQueries(File[] queryFilesSortedByName) throws IOException{
    BigTable timesTable = BigTable.readFromFile(DATA_FILE);
    int N = 14;
    for (int size = 1; size <= N; size++){
      StringBuilder b = new StringBuilder();
      SortedMap<Integer, Double> solvables = new TreeMap<Integer, Double>();
      List<Integer> timesForSize = timesTable.intRow(size - 1);//0-th row for size 1
      timesForSize = timesForSize.subList(1, timesForSize.size());//1st column is the size
      int allTimes = timesForSize.size();
      Collections.sort(timesForSize);
      for (int i = 0; i < allTimes; i++){
        int time = timesForSize.get(i);
        double percentage = (i * 100.0) / (allTimes - 1);
        solvables.put(time, percentage);//replaces any old mapping on purpose to take the last
      }
      for (int time : solvables.keySet()){
        System.out.println(time + " " + solvables.get(time));
        b.append(time).append(" ").append(solvables.get(time)).append(Utils.newLine);
      }
      Files.writeToFile(b.toString(), "wsu_solvable_" + size + ".data");
    }

    StringBuilder gplot = new StringBuilder();
    gplot.append("set log x" + Utils.newLine);
    gplot.append("set ylabel \"solvable queries (%)\"" + Utils.newLine);
    gplot.append("set xlabel \"time (ms)\"" + Utils.newLine);
    gplot.append("set ylabel font \",15\"" + Utils.newLine);
    gplot.append("set xlabel font \",15\"" + Utils.newLine);
    gplot.append("set data style lines" + Utils.newLine);
    gplot.append("set terminal postscript eps enhanced monochrome" + Utils.newLine);
    gplot.append("set output \"" + "wsu_solvable.eps" + "\"" + Utils.newLine);
    gplot.append("plot \\" + Utils.newLine);
    for (int size = 1; size <= N; size++){
      gplot.append("\"" + "wsu_solvable_" + size + ".data" + "\" title \"size " + size + "\" with lines");
      if (size != N){
        gplot.append(", \\");
      }
      gplot.append(Utils.newLine);
    }
    Files.writeToFile(gplot.toString(), "wsu_solvable" + ".gplot");
    GNUPlot.runGNUplot(new File("wsu_solvable" + ".gplot"));
  }

  private static void checkSatisfiableQueries(File[] queryFilesSortedByName, boolean[] satisfiable, BigTable satTable){
    for (int i = 0; i < satisfiable.length; i++){
      List<Integer> satSizes = satSizes(satTable, i + 1);
      if (satisfiable[i]){
        if (satSizes.isEmpty()){
          System.out.println(queryFilesSortedByName[i]);
          System.out.println(satSizes);
        }
      }else{
        if (!satSizes.isEmpty())
          throw new  IllegalStateException("expected UNSAT for " + queryFilesSortedByName[i] + " sizes:" + satSizes) ;
      }
    }
  }

  private static boolean[] findSatisfiableQueries(File[] queryFilesSortedByName) throws IOException{
    boolean[] satisfiable = new boolean[queryFilesSortedByName.length];
    for (int i = 0; i < queryFilesSortedByName.length; i++){
      File queryFile = queryFilesSortedByName[i];
      String fileContents = Files.getFileContents(queryFile);
      boolean isSatisfiable = fileContents.contains("ISEMPTY=false");
      satisfiable[i] = isSatisfiable;
    }
    return satisfiable;
  }

  private static void printRatioOfSATperN(boolean[] satisfiable, BigTable satTable){
    int allSatisfiable = countTrue(satisfiable);
    for (int row = 0; row < satTable.rowCount(); row++){
      int count= 0;
      for (int column = 1; column < satTable.columnCount(row); column++){
        boolean isSat = isSATUpToSize(satTable, row + 1, column);
        if (isSat){
          count++;
        }
      }
      System.out.println("Size " + (row + 1) + " sat:" + count + " of " + allSatisfiable + " ratio:" + (count * 1.0 / allSatisfiable));
    }
  }

  private static void plotGrammarSizeVsTime(File[] queryFilesSortedByName, boolean[] satisfiable) throws IOException,RecognitionException{
    //print scatter plot data for grammarsize vs. time at length 4
    int N = 4;
    StringBuilder dataSAT = new StringBuilder();
    StringBuilder dataUNSAT = new StringBuilder();
    List<Integer> sizes = new ArrayList<Integer>();
    BigTable timeTable = BigTable.readFromFile(DATA_FILE);
    for (int i = 0; i < queryFilesSortedByName.length; i++){
      System.out.println(i + " of " + queryFilesSortedByName.length);
      File queryFile = queryFilesSortedByName[i];
      int grammarSize = grammarSize(queryFile, N);
      sizes.add(grammarSize);
      int solveTime = Integer.valueOf(timeTable.cell(N - 1, i + 1));//first column is size, so we skip that
      boolean isSAT = satisfiable[i];
      if (isSAT){
        dataSAT.append(grammarSize).append(" ").append(solveTime).append(Utils.newLine);
      }else{
        dataUNSAT.append(grammarSize).append(" ").append(solveTime).append(Utils.newLine);
      }
    }
    System.out.println("Mean grammar size:" + CollectionsExt.meanInts(sizes));
    System.out.println("Std dev. grammar size:" + CollectionsExt.stddevInts(sizes, false));
    System.out.println("Min grammar size:" + Collections.min(sizes));
    System.out.println("Max grammar size:" + Collections.max(sizes));

    String sizeTimeDataSATFileName = "wsu_sizeTime_sat.data";
    String sizeTimeDataUNSATFileName = "wsu_sizeTime_unsat.data";
    String sizeTimeGplotFileName = "wsu_sizeTime.gplot";
    String sizeTimeOutputFileNameEPS = "wsu_sizeTime.eps";
    Files.writeToFile(dataSAT.toString(), sizeTimeDataSATFileName);
    Files.writeToFile(dataUNSAT.toString(), sizeTimeDataUNSATFileName);
    StringBuilder gplot = new StringBuilder();
    gplot.append("set log y" + Utils.newLine);
    gplot.append("set log x" + Utils.newLine);
    gplot.append("set ylabel \"solving time (sec.)\"" + Utils.newLine);
    gplot.append("set xlabel \"grammar size\"" + Utils.newLine);
    gplot.append("set key off" + Utils.newLine);
    gplot.append("set ylabel font \"Arial,20\"" + Utils.newLine);
    gplot.append("set xlabel font \"Arial,20\"" + Utils.newLine);
    gplot.append("set terminal postscript eps enhanced monochrome" + Utils.newLine);
    gplot.append("set output \"" + sizeTimeOutputFileNameEPS + "\"" + Utils.newLine);
    gplot.append("plot \"" + sizeTimeDataSATFileName + "\" using 1:($2/1000) with points pointtype 1 title \"SAT\",\\" + Utils.newLine);
    gplot.append("     \"" + sizeTimeDataUNSATFileName + "\" using 1:($2/1000) with points pointtype 6 title \"UNSAT\"" + Utils.newLine);
    Files.writeToFile(gplot.toString(), sizeTimeGplotFileName);
    GNUPlot.runGNUplot(new File(sizeTimeGplotFileName));
  }

  private static int grammarSize(File queryFile, int n) throws IOException,RecognitionException{
    String constraint = ExperimentWSU.instantiateTemplate(n, Files.getFileContents(queryFile));
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    InputStream istream = new ByteArrayInputStream(constraint.getBytes());
    HProgram parse = HProgramParser.parse(baos, istream);
    return cfgSize(parse);
  }

  //size of the CFG in this hampi 'program'. The size is the number of all elements in all productions (empty production also counts as 1).
  private static int cfgSize(HProgram parse){
    int size = 0;
    List<HStatement> cfgStatements = parse.getStatements(HGrammarElementKind.STMT_CFG);
    for (HStatement stmt : cfgStatements){
      CFGStatement cfgStmt = (CFGStatement) stmt;
      List<List<CFGProductionElement>> elementSets = cfgStmt.getElementSets();
      for (List<CFGProductionElement> productionElemens : elementSets){
        size += productionElemens.isEmpty() ? 1 : productionElemens.size();
      }
    }
    return size;
  }

  private static boolean isSATUpToSize(BigTable satTable, int size, int column){
    boolean upToSize = false;
    for (int i = 1; i <= size; i++){
      boolean satAtSize = 1 == Integer.valueOf(satTable.cell(i - 1, column).trim());
      upToSize = upToSize || satAtSize;
    }
    return upToSize;
  }

  private static int countTrue(boolean[] satisfiable){
    int count = 0;
    for (boolean sat : satisfiable){
      count += (sat ? 1 : 0);
    }
    return count;
  }

  private static List<Integer> satSizes(BigTable satTable, int column){
    List<Integer> result = new ArrayList<Integer>(satTable.rowCount());
    for (int row = 0; row < satTable.rowCount(); row++){
      if (Integer.valueOf(satTable.cell(row, column)) == 1){
        result.add(row + 1);//size is row+1
      }
    }
    return result;
  }

}
