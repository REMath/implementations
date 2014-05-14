package hampi.experiments;

import hampi.utils.*;

import java.io.*;
import java.util.*;

/**
 * This performs an experiment in which increasing number of 'contains'
 * constraints are composed. The purpose is to evaluate Hampi's performance on
 * intersection constraints (PSPACE-complete problem) and to compare to
 * CFGAnalyzer and PEX. The strings are read from the given file.
 */
public final class ExperimentIndexOfProgression{

  public static void main(String[] args) throws Exception{
    if (args.length != 2){
      System.out.println("Usage: inputFile outputDir");
      System.out.println("  inputFile contains the strings");
      System.out.println("  outputDir is where the results are placed");
      System.exit(1);
      return;
    }
    File f = new File(args[0]);
    if (!f.exists() || !f.isFile())
      throw new IllegalStateException("File does not exist " + f.getAbsolutePath());
    File outputDir = new File(args[1]);
    if (!outputDir.exists()){
      outputDir.mkdirs();
    }

    //duplicate all output to log 
    System.setErr(System.out);
    File logFile = new File(outputDir, "indexOf_log.txt");
    System.setOut(new PrintStream(Files.tee(System.out, new FileOutputStream(logFile))));
    System.out.println(new Date() + " start");
    System.out.println("Logging to " + logFile.getAbsolutePath());
    System.out.println("arguments: " + CollectionsExt.join(" ", args));
    runIndexOfExperiment(f, outputDir);
    System.out.println(new Date() + " finished");
  }

  private static void runIndexOfExperiment(File f, File outputDir) throws IOException,Exception{
    SolverExperimentResultSet<Pair<Boolean, Double>> hampiResults = new SolverExperimentResultSet<Pair<Boolean, Double>>("hampi solver");
    SolverExperimentResultSet<Pair<Boolean, Double>> cfgResults = new SolverExperimentResultSet<Pair<Boolean, Double>>("cfganalyzer");
    List<String> strs = Files.readWhole(f);
    for (int i = 1; i <= strs.size(); i++){
      intersect(strs.subList(0, i), hampiResults, cfgResults);

      SolverExperimentResultSet<Double> timeRatio = SolverExperimentResultSet.timeRatio(cfgResults, hampiResults, 0);
      HampiExperiments.createResultGraphs(hampiResults, cfgResults, f.getName(), timeRatio, outputDir);
      HampiExperiments.printInRatioOrder(strs.size(), timeRatio);
    }
  }

  /**
   * Create a constraint that asks for a string that contains all strings. Do
   * this in Hampi and CFGAnalyzer.
   */
  private static void intersect(List<String> strs, SolverExperimentResultSet<Pair<Boolean, Double>> hampiResults, SolverExperimentResultSet<Pair<Boolean, Double>> cfgResults) throws Exception{
    runHampi(hampiResults, strs);
    runCFGAnalyzer(cfgResults, strs);
  }

  /**
   * Runs CFG analyzer and tries to find a string that contains all strings in
   * strs.
   * 
   */
  private static void runCFGAnalyzer(SolverExperimentResultSet<Pair<Boolean, Double>> cfgResults, List<String> strs) throws IOException{
    File[] cfgFiles = new File[strs.size()];
    for (int i = 0; i < strs.size(); i++){
      File f = File.createTempFile("cfg", null);
      String cfgGrammarForContains = cfgGrammarForContains(strs.get(i));
      cfgFiles[i] = Files.writeToFile(cfgGrammarForContains, f);
    }
    StringBuilder out = new StringBuilder();
    Pair<Boolean, Double> p = CFGAnalyzer.runIntersection(lengthSum(strs), out, cfgFiles);
    System.out.println("cfg " + strs.size() + p);
    assert p.first : "expected SAT for " + strs + Arrays.toString(cfgFiles) + out;
    cfgResults.addResult("indexOf", strs.size(), p);
    for (File file : cfgFiles){
      file.delete();
    }
  }

  /**
   * Creates a CFGAnalyzer grammar that encodes: Sigma* s Sigma*. The grammar is<br>
   * <br>
   * S : SigmaStar s SigmaStar; //a will need to be split into characters<br>
   * SigmaStar : | Sigma SigmaStar;<br>
   * Sigma : "a" | "b" ...;<br>
   */
  private static String cfgGrammarForContains(String s){
    StringBuilder b = new StringBuilder();
    b.append("S : SigmaStar " + splitIntoQuitedChars(s) + " SigmaStar;\n");
    b.append("SigmaStar : ; \n");
    b.append("          : Sigma SigmaStar;\n");

    b.append("Sigma ");
    String[] range = allLetterAlphabet();
    for (int i = 0; i < range.length; i++){
      b.append(": \"").append(range[i]).append("\";\n");
    }
    return b.toString();
  }

  /**
   * Returns s split into quoted chars. foo -> "f" "o" "o"
   */
  private static String splitIntoQuitedChars(String s){
    StringBuilder b = new StringBuilder();
    for (char c : s.toCharArray()){
      b.append("\"").append(c).append("\" ");
    }
    return b.toString();
  }

  /**
   * Creates and solves a Hampi constraint that finds a string that contains all
   * substrings.
   */
  private static void runHampi(SolverExperimentResultSet<Pair<Boolean, Double>> hampiResults, List<String> strs) throws IOException{
    String hampiConstraint = createHampiConstraint(strs);
    Pair<Boolean, Double> p = HampiExperiments.solveConstraint(hampiConstraint, null);
    assert p.first : "expected SAT";
    System.out.println("hampi " + strs.size() + " " + p);
    hampiResults.addResult("indexOf", strs.size(), p);
  }

  private static String createHampiConstraint(List<String> strs){
    StringBuilder b = new StringBuilder();
    int length = lengthSum(strs);
    b.append("var v : " + length + ";\n");
    for (String s : strs){
      b.append("assert v contains \"" + s + "\";\n");
    }
    return b.toString();
  }

  /**
   * Sum of string lengths.
   */
  private static int lengthSum(List<String> strs){
    int res = 0;
    for (String s : strs){
      res += s.length();
    }
    return res;
  }

  private static String[] createStringsMedium(){
    return new String[] {//
    "thiszero", //
        "thisone",//
        "thistwo",//
        "thisthree",//
        "thisfour",//
        "thisfive",//
        "thissix",//
        "thisseven",//
        "thiseigth",//
        "thisnine",//
        "thisten",//
        "thiseleven",//
        "thistwelve",//
    };
  }

  private static String[] allLetterAlphabet(){
    char[] az = ASCIITable.range('a', 'z');
    char[] AZ = ASCIITable.range('A', 'Z');
    String[] strings = new String[az.length + AZ.length];
    for (int i = 0; i < az.length; i++){
      strings[i] = String.valueOf(az[i]);
    }
    for (int i = 0; i < AZ.length; i++){
      strings[i + az.length] = String.valueOf(AZ[i]);
    }
    return strings;
  }
}
