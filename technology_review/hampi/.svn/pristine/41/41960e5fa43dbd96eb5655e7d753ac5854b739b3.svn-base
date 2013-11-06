package hampi.experiments;

import hampi.utils.*;

import java.io.File;
import java.util.*;

/**
 * Generates random lists of cfg files from the given directory.
 */
public final class GenerateCFGFileLists{

  public static void main(String[] args){
    if (args.length != 4){
      System.out.println("usage: seed n m dir");
      System.out.println(" where seed is the random seed (e.g., 0)");
      System.out.println(" n is the number of files per line");
      System.out.println(" m is the number of lines");
      System.out.println(" dir is the directory that contains the files");
      System.exit(1);
      return;
    }
    Randomness.reset(Long.parseLong(args[0]));
    int n = Integer.parseInt(args[1]);
    int m = Integer.parseInt(args[2]);
    String dir = args[3];
    assert n > 0 && m > 0;

    List<File> files = Files.findFilesInDir(new File(dir), "", ".cfg");
    Collections.sort(files);

    List<List<File>> fnamelists = CollectionsExt.allCombinations(CollectionsExt.repeat(files, n));
    Collections.shuffle(fnamelists, Randomness.getRandom());

    File workingDir = new File(System.getProperty("user.dir"));

    int count = 0;
    int idx = 0;
    while (count < m){
      List<File> flist = fnamelists.get(idx);
      idx++;
      if (!skipList(flist)){
        count++;
        for (File file : flist){
          System.out.print(Files.relative(file, workingDir));
          System.out.print(" ");
        }
        System.out.println();
      }
    }
  }

  private static boolean skipList(List<File> flist){
    for (File file : flist){
      if (HampiExperiments.skipFile(file.getName()))
        return true;
    }
    return false;
  }
}
