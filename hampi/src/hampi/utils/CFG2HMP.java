package hampi.utils;

import java.io.*;
import java.util.*;

/**
 * This class converts CFGAnalyser problem instances to Hampi problem instances.
 * Handles <br>
 * emptiness<br>
 * intersection<br>
 * universality<br>
 * inclusion<br>
 * equivalence<br>
 */
public class CFG2HMP{
  private static final String       MODE_EMPTINESS    = "-e";
  private static final String       MODE_HELP         = "-h";
  private static final String       MODE_INTERSECT    = "-n";
  private static final String       MODE_INCLUSION    = "-i";
  private static final String       MODE_UNIVERSALITY = "-u";
  /*XXX can we do equivalence without extending the lang to handle 'OR' in asserts?*/
  private static final String       MODE_EQUIVALENCE  = "-q";
  private static final List<String> MODES             = Arrays.asList(MODE_EMPTINESS, MODE_INTERSECT, MODE_HELP, MODE_INCLUSION, MODE_UNIVERSALITY /*"-q",*/);

  public static void main(String[] args) throws IOException{
    if (args.length < 4){
      printUsage();
      return;
    }
    int size = getSize(args);
    String mode = getMode(args);
    String[] fileNames = getFileNames(args);
    if (!isOKUsage(size, mode, fileNames)){
      printUsage();
      return;
    }
    if (mode.equals(MODE_EMPTINESS)){
      String cons = convertToEmptinessConstraint(size, fileNames[0]);
      System.out.println(cons);
    }else if (mode.equals(MODE_UNIVERSALITY)){
      String cons = convertToUniversalityConstraint(size, fileNames[0]);
      System.out.println(cons);
    }else if (mode.equals(MODE_INTERSECT)){
      String cons = convertToIntersectionConstraint(size, fileNames);
      System.out.println(cons);
    }else if (mode.equals(MODE_INCLUSION)){
      String cons = convertToInclusionConstraint(size, fileNames[0], fileNames[1]);
      System.out.println(cons);
    }else{
      printUsage();
    }
  }

  /**
   * Reads a cfg file and creates a Hampi universality constraint for the given
   * size.
   */
  public static String convertToUniversalityConstraint(int size, String fname) throws IOException{
    String hg = readAndConvertToHampiGrammar(fname, "");
    StringBuilder b = new StringBuilder();
    b.append(createHampiEmptinessConstraint(hg, size, "1", true, false));
    b.append(createHampiEmptinessConstraint(sigmaStarGrammar(hg), size, "2", false, false));
    return b.toString();
  }

  /**
   * Returns the grammar that generates all strings form the alphabet of
   * terminals of the given Hampi grammar.
   */
  private static String sigmaStarGrammar(String hg){
    Set<String> terminals = getTerminals(hg);
    StringBuilder b = new StringBuilder();
    String ntName = "SigmaStar";
    b.append("cfg " + ntName + " := ");
    for (Iterator<String> iter = terminals.iterator(); iter.hasNext();){
      String term = iter.next();
      b.append(term).append(" | ").append(term).append(" " + ntName + " ");
      if (iter.hasNext()){
        b.append(" | ");
      }
    }
    b.append(";");
    return b.toString();
  }

  /**
   * Returns the set of terminals in the hmp or cfg grammar (both formats work).
   */
  public static Set<String> getTerminals(String hg){
    Scanner s = new Scanner(hg);
    Set<String> res = new LinkedHashSet<String>();
    while (s.hasNext()){
      String token = s.next();
      if (token.startsWith("\"") && token.endsWith("\"")){
        res.add(token);
      }
    }
    return res;
  }

  /**
   * Reads a cfg file and creates a Hampi inclusion constraint for the given
   * size.
   */
  public static String convertToInclusionConstraint(int size, String fname1, String fname2) throws IOException{
    if (fname1.equals(fname2))
      return createUNSATconstraint();//if both grammars are the same, then there is no string in the diff, so UNSAT.
    String hg1 = readAndConvertToHampiGrammar(fname1, String.valueOf(1));
    String hg2 = readAndConvertToHampiGrammar(fname2, String.valueOf(2));
    StringBuilder b = new StringBuilder();
    b.append(createHampiEmptinessConstraint(hg1, size, String.valueOf(1), true, true));
    b.append(createHampiEmptinessConstraint(hg2, size, String.valueOf(2), false, false));
    return b.toString();
  }

  /**
   * Reads a cfg file and creates a Hampi intersection constraint for the given
   * size.
   */
  public static String convertToIntersectionConstraint(int size, String... fileNames) throws IOException{
    List<String> fnames = new ArrayList<String>(new TreeSet<String>(Arrays.asList(fileNames)));
    if (fnames.size() == 1)
      return convertToEmptinessConstraint(size, fileNames[0]);//in case all file names are the same
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < fileNames.length; i++){
      String fname = fnames.get(i);
      String hg = readAndConvertToHampiGrammar(fname, String.valueOf(i));
      b.append(createHampiEmptinessConstraint(hg, size, String.valueOf(i), i == 0, true));
    }
    return b.toString();
  }

  /**
   * Reads a cfg file and creates a Hampi emptiness constraint for the given
   * size.
   */
  public static String convertToEmptinessConstraint(int size, String cfgFileName) throws IOException{
    String hampiGrammar = readAndConvertToHampiGrammar(cfgFileName, "");
    return createHampiEmptinessConstraint(hampiGrammar, size, "", true, true);
  }

  /**
   * Converts CFG-format grammar and converts to Hampi grammar. Each
   * nonterminal's name is suffixed (so that we can distinguish them in
   * intersection etc). Note: the nonterminal renaming is not a full solution -
   * you can still get name clashes. We're going to ignore that.
   */
  private static String readAndConvertToHampiGrammar(String cfgFileName, String nonterminalNameSuffix) throws IOException{
    String contents = Files.getFileContents(cfgFileName);
    return convertToHampiGrammar(contents, nonterminalNameSuffix);
  }

  /**
   * Creates a constraint that says: there's is a string of the given length in
   * the grammar. Hampi will then find the string.
   */
  public static String createHampiEmptinessConstraint(String hampiGrammar, int length, String nameSuffix, boolean includeVarDecl, boolean isIn){
    String mainNonterminal = getMainNonterminalName(hampiGrammar);
    StringBuilder b = new StringBuilder();
    if (includeVarDecl){
      b.append("var hampiStringVar : ###;\n");
    }
    b.append(hampiGrammar);
    b.append("\nreg limit" + nameSuffix + " := fix(" + mainNonterminal + ", ###);\n");
    if (isIn){
      b.append("assert hampiStringVar in limit" + nameSuffix + ";\n");
    }else{
      b.append("assert hampiStringVar not in limit" + nameSuffix + ";\n");
    }
    return b.toString().replace("###", String.valueOf(length));
  }

  /**
   * Returns the name of the first nonterminal in the grammar. Assumes that the
   * nonterminal is the first symbol after 'cfg'.
   */
  public static String getMainNonterminalName(String hampiGrammar){
    return new Scanner(hampiGrammar).skip("cfg").next();//first token after 'cfg'
  }

  /**
   * Creates a simple UNSAT constraint
   */
  private static String createUNSATconstraint(){
    StringBuilder b = new StringBuilder();
    b.append("var v : 1;\n");
    b.append("assert v contains \"x\";\n");
    b.append("assert v contains \"y\";\n");
    return b.toString();
  }

  //cfg2hmp -s <k> mode <file1> [<file2> ...]
  private static int getSize(String[] args){
    if (!args[0].equals("-s"))
      return -1;
    try{
      return Integer.valueOf(args[1]);
    }catch (NumberFormatException e){
      return -1;
    }
  }

  /**
   * Returns the mode of conversion.
   */
  private static String getMode(String[] args){
    return args[2];
  }

  /**
   * Returns the names of files passed as arguments.
   */
  private static String[] getFileNames(String[] args){
    String[] result = new String[args.length - 3];
    System.arraycopy(args, 3, result, 0, result.length);
    return result;
  }

  private static boolean isOKUsage(int size, String mode, String[] fileNames){
    if (size < 0)
      return false;
    if (!MODES.contains(mode))
      return false;
    if (fileNames.length == 0 && !mode.equals(MODE_HELP))
      return false;
    for (String fName : fileNames){
      File f = new File(fName);
      if (!f.exists() || f.isDirectory()){
        System.out.println("ERROR File:" + f.getAbsolutePath() + " does not exist");
        return false;
      }
    }
    if (mode.equals(MODE_EMPTINESS) && fileNames.length != 1)
      return false;
    if (mode.equals(MODE_UNIVERSALITY) && fileNames.length != 1)
      return false;
    if (mode.equals(MODE_INTERSECT) && fileNames.length < 2)
      return false;
    if (mode.equals(MODE_INCLUSION) && fileNames.length != 2)
      return false;
    return true;
  }

  private static void printUsage(){
    System.out.println("Usage: cfg2hmp -s <k> mode <file1> [<file2> ...]");
    System.out.println("Converts a problem instance for CFGAnalyzer to a problem instance of Hampi. ");
    System.out.println("Files are assumed to contain grammars G1, G2, ...");
    System.out.println("Comments in the grammars are lost on conversion.");
    System.out.println("The result is printed to the standard output.");
    System.out.println("");
    System.out.println(" Parameters ");
    System.out.println("  -s <k>");
    System.out.println("  size k of the string, k >= 1");
    System.out.println();
    System.out.println(" Mode is one of");
    System.out.println("  " + MODE_EMPTINESS + " ");
    System.out.println("   checks whether L(G1) is not empty");
    System.out.println("   a counterexample will be a word in L(G1)");
    System.out.println();
    System.out.println("  " + MODE_UNIVERSALITY + " ");
    System.out.println("   checks whether L(G1) is not universal");
    System.out.println("   a counterexample will be a word not in L(G1)");
    System.out.println();
    System.out.println("  " + MODE_INCLUSION + " ");
    System.out.println("   checks whether L(G1) is not included in L(G2)");
    System.out.println("   a counterexample will be a word w in L(G1) \\ L(G2)");
    System.out.println();
    System.out.println("  " + MODE_INTERSECT + " ");
    System.out.println("   checks whether the intersection of L(G1), L(G2), ... is empty");
    System.out.println("   an example will be a word w in all of them");
    //    System.out.println();
    //    System.out.println("  -q ");
    //    System.out.println("   checks whether the L(G1)=L(G2)");
    //    System.out.println("   a counterexample will be a word w in one language but not the other");
    System.out.println();
    System.out.println("  " + MODE_HELP + "  Display this list of options");
  }

  /**
   * Converts the CFGAnalyzerGrammar to Hampi grammar. Optionally, each
   * nonterminal name can be suffixed with a string (to rename the nonterminal).
   */
  public static String convertToHampiGrammar(String cfgAnalyzerGrammar, String nonterminalNameSuffix){
    String cfgGrammarNoComments = removeComments(cfgAnalyzerGrammar);
    List<String> tokens = new ArrayList<String>();
    Scanner scanner = new Scanner(cfgGrammarNoComments);
    String curr = scanner.next();
    String lookAhead = null;
    while (scanner.hasNext()){
      lookAhead = scanner.next();
      if (curr.equals(";") && lookAhead.equals(":")){
        tokens.add("|");
        curr = scanner.next();
        lookAhead = curr;
      }else if (curr.equals(";")){
        tokens.add(";NEWLINE");
        curr = lookAhead;
      }else if (curr.equals(":")){
        tokens.add(":= ");
        curr = lookAhead;
        tokens.add(tokens.size() - 2, "cfg");
      }else if (curr.startsWith("\"")){//terminal
        tokens.add(curr);
        curr = lookAhead;
      }else{//nonterminal
        tokens.add(curr + nonterminalNameSuffix);
        curr = lookAhead;
      }
    }
    tokens.add(lookAhead);
    String hampiGrammar = CollectionsExt.join(" ", tokens);
    return hampiGrammar.replace("NEWLINE" + " ", "\n");
  }

  private static String removeComments(String contents){
    StringBuilder b = new StringBuilder();
    //read the whole file, skip the comments
    int i = 0;
    int length = contents.length();
    while (i + 1 < length){
      String s = contents.substring(i, i + 2);
      if (s.equals("/*")){
        boolean inComment = true;
        while (i + 1 < length && inComment){
          i++;
          s = contents.substring(i, i + 2);
          inComment = !s.equals("*/");
          if (!inComment){
            i++;
          }
        }
      }else{
        b.append(contents.charAt(i));
      }
      i++;
    }
    b.append(contents.charAt(length - 1));

    return b.toString();
  }

}
