package hampi.experiments;

import hampi.HampiOptions;
import hampi.utils.Command;

import java.io.*;

/**
 * Runs GNUplot.
 */
public final class GNUPlot{

  private static final String EXECUTABLE = HampiOptions.INSTANCE.get("gnuplot");

  /**
   * Runs the GNUPlot script.
   */
  public static void runGNUplot(File gplotFile){
    OutputStream os = new ByteArrayOutputStream();
    int exec = Command.exec(EXECUTABLE + " " + gplotFile, new PrintStream(os));
    if (exec != 0)
      throw new IllegalStateException("cannot run " + gplotFile + "\n" + os);
  }

}
