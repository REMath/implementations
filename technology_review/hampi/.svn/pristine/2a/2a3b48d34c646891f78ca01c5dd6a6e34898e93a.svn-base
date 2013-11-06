package hampi.experiments;

import static hampi.experiments.HampiExperiments.REPEAT;
import hampi.utils.*;

import java.io.*;

/**
 * Runs the CFG analyzer.
 */
public final class CFGAnalyzer{

  private CFGAnalyzer(){
    throw new IllegalStateException("do not instantiate");
  }

  /**
   * Runs emptiness query for given size. Returns if SAT. Appends output to out
   * (out may be null).
   */
  public static Pair<Boolean, Double> runEmptiness(int size, StringBuilder out, File cfgFile){
    return run(size, out, "-e", cfgFile);
  }

  /**
   * Runs an intersection CFGAnalyzer query. Returns a pair of SAT, mean time.
   * If out is provided, the output stream of the *last* execution of
   * cfganalyzer is appended to out.
   */
  public static Pair<Boolean, Double> runIntersection(int size, StringBuilder out, File... files){
    if (files.length == 1)
      return runEmptiness(size, out, files[0]);
    return run(size, out, "-n", files);
  }

  /**
   * Runs a multi-file CFGAnalyzer query. Returns a pair of SAT, mean time. If
   * out is provided, the output stream of the *last* execution of cfganalyzer
   * is appended to out.
   */
  public static Pair<Boolean, Double> run(int size, StringBuilder out, String option, File... files){
    String[] command = new String[6 + files.length];
    command[0] = "lib/cfganalyzer-2007-12-03/bin/cfganalyzer";
    command[1] = "-b";
    command[2] = String.valueOf(size);
    command[3] = "-m";
    command[4] = String.valueOf(size);
    command[5] = option;
    for (int i = 0; i < files.length; i++){
      command[6 + i] = files[i].getAbsolutePath();
    }

    boolean isSat = false;
    long[] times = new long[REPEAT];
    OutputStream os = new ByteArrayOutputStream();
    PrintStream blackHole = new PrintStream(os);
    for (int r = 0; r < REPEAT; r++){
      StopWatch watch = new StopWatch("");
      watch.start();
      int exec = Command.exec(command, blackHole);
      watch.stop();
      isSat = exec == 0;
      if (exec != 1 && exec != 0)
        throw new IllegalStateException(os.toString());
      times[r] = watch.getTotal();

      if (out != null && r == REPEAT - 1){
        out.append(os);
      }
    }
    return Pair.create(isSat, CollectionsExt.mean(times));
  }
}
