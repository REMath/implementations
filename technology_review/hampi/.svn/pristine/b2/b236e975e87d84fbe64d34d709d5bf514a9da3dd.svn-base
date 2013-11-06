package hampi.experiments;

import hampi.utils.*;

import java.io.*;
import java.text.DecimalFormat;
import java.util.*;

/**
 * Represents results from a solving experiment.<br>
 * Each experiment consists of a set of named problem instances and data points
 * (problem sizes) for each instance. For each problem instance and problem
 * size, the result can be the solving time, or whether the problem has a
 * solution for the given size or not, or a log ratio of solving times for
 * different solvers.<br>
 */
public class SolverExperimentResultSet<T> implements Serializable{
  private static final long serialVersionUID = 5374646895126155761L;

  /**
   * Formats the results. Subclass and override the format method to customize.
   */
  public static class ResultFormatter<T> implements Serializable{
    private static final long serialVersionUID = -6787140134386290338L;

    public String format(T t){
      return String.valueOf(t);
    }
  }

  /**
   * Default formatter for doubles. Uses pattern "#####.###".
   */
  public static final ResultFormatter<Double> DOUBLE_FORMATTER = new ResultFormatter<Double>(){
    private static final long serialVersionUID = 4979228945353565945L;
    DecimalFormat df = new DecimalFormat("########.######");

    @Override
    public String format(Double t){
      assert t != null;
      return df.format(t);
    }
  };

  /**
   * Default formatter for double,double. Uses pattern "#####.###" for both and
   * separates them by space.
   */
  public static final ResultFormatter<Pair<Double, Double>> DOUBLE_DOUBLE_FORMATTER = new ResultFormatter<Pair<Double, Double>>(){
    private static final long serialVersionUID = 1190169872321833171L;
    ResultFormatter<Double> f = DOUBLE_FORMATTER;

    @Override
    public String format(Pair<Double, Double> t){
      assert t != null;
      return f.format(t.first) + " " + f.format(t.second);
    }
  };

  /**
   * Default formatter for doubles. Uses pattern "#####.###". Ignores the
   * boolean.
   */
  public static final ResultFormatter<Pair<Boolean, Double>> BOOLEAN_DOUBLE_FORMATTER = new ResultFormatter<Pair<Boolean, Double>>(){
    private static final long serialVersionUID = 6501308516827964121L;
    ResultFormatter<Double> f = DOUBLE_FORMATTER;

    @Override
    public String format(Pair<Boolean, Double> t){
      assert t != null;
      return f.format(t.second);
    }
  };

  //name of the experiment
  private final String name;

  //results of the experiment
  private final DoubleKeyMap<String, Integer, T> results = new DoubleKeyMap<String, Integer, T>();

  public SolverExperimentResultSet(String name){
    this.name = name;
  }

  public void addResult(String problemName, int problemSize, T t){
    assert t != null;
    results.put(problemName, problemSize, t);
  }

  @Override
  public String toString(){
    return name + "\n" + results.toString();
  }

  public T getResult(String problemName, int problemSize){
    assert problemName != null;
    assert problemSize >= 0;
    return results.get(problemName, problemSize);
  }

  /**
   * Returns the results, each experiment in separate column, each problem size
   * in separate row. If an experiment is missing a result for a given size, 0
   * is used.
   */
  public String asGNUPlotDataFileContent(ResultFormatter<T> rf){
    int maxSize = maxSize();
    if (maxSize == -1)
      return "";
    StringBuilder s = new StringBuilder();
    assert maxSize >= 0 : maxSize;
    for (int size = minSize(); size <= maxSize; size++){
      s.append(size + " ");
      for (String name : new TreeSet<String>(getExperimentNames())){//sort experiments by name
        T result = getResult(name, size);
        assert result != null;
        s.append(rf.format(result) + " ");
      }
      s.append(Utils.nl);
    }
    return s.toString();
  }

  /**
   * Returns the minimum size for any instance in this set. Returns MAX_VALUE if
   * there is no instance in this set.
   */
  private int minSize(){
    int min = Integer.MAX_VALUE;
    for (String name : getExperimentNames()){
      min = Math.min(min, Collections.min(results.getK2Set(name)));
    }
    return min;
  }

  /**
   * Returns the maximum size for any instance in this set. Returns -1 if there
   * is no instance in this set.
   */
  public int maxSize(){
    int max = -1;
    for (String name : getExperimentNames()){
      max = Math.max(max, Collections.max(results.getK2Set(name)));
    }
    return max;
  }

  public int experimentCount(){
    return getExperimentNames().size();
  }

  public String asGNUPlotFileContent(File dir, String dataFileName, String outputfileName, String ylabel, boolean lineTitles){
    String nl = Utils.nl;
    String outputFileFullName = dir.getName() + "/" + outputfileName;
    String dataFileFullName = dir.getName() + "/" + dataFileName;

    StringBuilder s = new StringBuilder();
    //    s.append("set key outside left" + nl);
    s.append("set title \"" + getName() + "\"" + nl);
    s.append("set log y" + nl);
    s.append("set xtics 1" + nl);
    s.append("set xtics rotate" + nl);
    s.append("set xtics font \"Arial,7\"" + nl);
    s.append("set ylabel \"" + ylabel + "\"" + nl);
    s.append("set xlabel \"" + "size" + "\"" + nl);
    s.append("set terminal svg" + nl);
    s.append("set output \"" + outputFileFullName + ".svg" + "\"" + nl);
    s.append("set data style lines" + nl);
    s.append("plot \\" + nl);
    List<String> sortedExperiementNames = new ArrayList<String>(new TreeSet<String>(getExperimentNames()));
    String lineTitle = " title \"" + (lineTitles ? sortedExperiementNames.get(0) : "") + "\"";
    s.append("'" + dataFileFullName + "'" + " using 1:2" + lineTitle + (experimentCount() == 1 ? "" : ", \\") + nl);
    for (int i = 1; i < experimentCount(); i++){
      String suffix = i == experimentCount() - 1 ? "" : ", \\";
      lineTitle = " title \"" + (lineTitles ? sortedExperiementNames.get(i) : "") + "\"";
      s.append("'" + "" + "'" + " using 1:" + (i + 2) + lineTitle + suffix + nl);
    }

    if (false){//XXX commented out because it does not work on some installations on gnuplot
      //plot in eps
      s.append("set term postscript eps" + nl);
      s.append("set output \"" + outputFileFullName + ".eps" + "\"" + nl);
      s.append("replot" + nl);
    }
    return s.toString();
  }

  public String asGNUPlotFileContentWithErrorbars(File dir, String dataFileName, String outputfileName, String ylabel){
    String nl = Utils.nl;
    String outputFileFullName = dir.getName() + "/" + outputfileName;
    String dataFileFullName = dir.getName() + "/" + dataFileName;
    StringBuilder s = new StringBuilder();
    //    s.append("set key outside left" + nl);
    s.append("set title \"" + getName() + "\"" + nl);
    s.append("set log y" + nl);
    s.append("set xtics 1" + nl);
    s.append("set xtics rotate" + nl);
    s.append("set xtics font \"Arial,7\"" + nl);
    s.append("set ylabel \"" + ylabel + "\"" + nl);
    s.append("set xlabel \"" + "size" + "\"" + nl);
    s.append("set terminal svg" + nl);
    s.append("set output \"" + outputFileFullName + ".svg" + "\"" + nl);
    s.append("set data style lines" + nl);
    s.append("plot \\" + nl);
    List<String> sortedExperiementNames = new ArrayList<String>(new TreeSet<String>(getExperimentNames()));
    String lineTitle = " title \"" + sortedExperiementNames.get(0) + "\"";
    String barsTitle = " title \"" + "stddev" + "\" ";
    s.append("'" + dataFileFullName + "'" + " using 1:2" + lineTitle + " with lines" + ", \\" + nl);
    s.append("'" + dataFileFullName + "'" + " using 1:2:3" + barsTitle + " with errorbars" + (experimentCount() == 1 ? "" : ", \\") + nl);
    for (int i = 1; i < experimentCount(); i++){//two columns per experim (value, stddev)
      String suffix = i == experimentCount() - 1 ? "" : ", \\";
      lineTitle = " title \"" + sortedExperiementNames.get(i) + "\"";
      s.append("'" + "" + "'" + " using 1:" + (2 * i + 2) + lineTitle + " with lines" + ", \\" + nl);
      s.append("'" + "" + "'" + " using 1:" + (2 * i + 2) + ":" + (2 * i + 3) + barsTitle + " with errorbars" + suffix + nl);
    }

    if (false){//XXX commented out because it does not work on some installations on gnuplot
      //plot in eps
      s.append("set term postscript eps" + nl);
      s.append("set output \"" + outputFileFullName + ".eps" + "\"" + nl);
      s.append("replot" + nl);
    }
    return s.toString();
  }

  public String getName(){
    return name;
  }

  /**
   * Creates a result set in which the results are ratios of times from the
   * argument results sets. Ignores experiments with time under a threshold.
   */
  public static <T> SolverExperimentResultSet<Double> timeRatio(SolverExperimentResultSet<Pair<T, Double>> r1, SolverExperimentResultSet<Pair<T, Double>> r2, long minTime){
    if (r1.isEmpty() || r2.isEmpty())
      return new SolverExperimentResultSet<Double>("time ratio");
    SolverExperimentResultSet<Double> result = new SolverExperimentResultSet<Double>("time ratio " + r1.getName() + " to " + r2.getName());
    Set<String> experims1 = r1.getExperimentNames();
    Set<String> experims2 = r2.getExperimentNames();
    @SuppressWarnings("unchecked")
    Set<String> commonExperims = CollectionsExt.intersection(experims1, experims2);
    for (String experim : commonExperims){
      Set<Integer> sizes1 = r1.getSizes(experim);
      Set<Integer> sizes2 = r2.getSizes(experim);
      @SuppressWarnings("unchecked")
      Set<Integer> commonSizes = CollectionsExt.intersection(sizes1, sizes2);
      double maxTime = 0;
      for (Integer size : commonSizes){
        double r1Time = r1.getResult(experim, size).second;
        double r2Time = r2.getResult(experim, size).second;
        maxTime = Math.max(maxTime, r1Time);
        maxTime = Math.max(maxTime, r2Time);
        double ratio = r1Time / r2Time;
        result.addResult(experim, size, ratio);
      }
      if (maxTime < minTime){
        result.remove(experim);
      }
    }
    return result;
  }

  public boolean isEmpty(){
    return results.isEmpty();
  }

  /**
   * Removes the experiment.
   */
  public void remove(String experim){
    results.remove(experim);
  }

  /**
   * Returns the set of problem sizes for the given problem instance.
   */
  public Set<Integer> getSizes(String experim){
    return results.getK2Set(experim);
  }

  /**
   * Returns the names of experiments.
   */
  public Set<String> getExperimentNames(){
    return results.getK1Set();
  }

  /**
   * Returns the list of argument pairs, in the order of results.
   */
  public List<Pair<String, Integer>> getPairsInOrder(final Comparator<T> comp){
    List<Pair<String, Integer>> res = new ArrayList<Pair<String, Integer>>();
    res.addAll(results.getK1K2Pairs());
    Collections.sort(res, new Comparator<Pair<String, Integer>>(){
      @Override
      public int compare(Pair<String, Integer> o1, Pair<String, Integer> o2){
        T r1 = getResult(o1.first, o1.second);
        T r2 = getResult(o2.first, o2.second);
        return comp.compare(r1, r2);
      }
    });
    return res;
  }

  /**
   * Takes a result set and returns a result set with 1 "experiment" that is the
   * average of the experiments in the set.<br>
   * The results are given as pairs <average, standard error>. <br>
   * NOTE: the silly name is because we need 2 methods and java can't
   * distinguish between generic methods.
   */
  public static SolverExperimentResultSet<Pair<Double, Double>> averageOfPairs(SolverExperimentResultSet<Pair<Boolean, Double>> r){
    SolverExperimentResultSet<Pair<Double, Double>> res = new SolverExperimentResultSet<Pair<Double, Double>>(r.getName() + " average");
    for (int i = r.minSize(), n = r.maxSize(); i <= n; i++){
      Set<String> experims = r.getExperimentForSize(i);
      Set<Double> times = new LinkedHashSet<Double>(experims.size());
      for (String exp : experims){
        Pair<Boolean, Double> result = r.getResult(exp, i);
        times.add(result.second);
      }
      Double avg = CollectionsExt.mean(times);
      Double stddev = CollectionsExt.stddev(times, false);

      res.addResult("average " + r.getName(), i, Pair.create(avg, stddev));
    }
    return res;
  }

  /**
   * Takes a result set and returns a result set with 1 "experiment" that is the
   * average of the experiments in the set.<br>
   * The results are given as pairs <average, standard error>.
   *
   * NOTE: the silly name is because we need 2 methods and java can't
   * distinguish between generic methods.
   */
  public static SolverExperimentResultSet<Pair<Double, Double>> averageOfDoubles(SolverExperimentResultSet<Double> r){
    SolverExperimentResultSet<Pair<Double, Double>> res = new SolverExperimentResultSet<Pair<Double, Double>>(r.getName() + " average");
    for (int i = r.minSize(), n = r.maxSize(); i <= n; i++){
      Set<String> experims = r.getExperimentForSize(i);
      Set<Double> times = new LinkedHashSet<Double>(experims.size());
      for (String exp : experims){
        Double result = r.getResult(exp, i);
        times.add(result);
      }
      Double avg = CollectionsExt.mean(times);
      Double stddev = CollectionsExt.stddev(times, false);

      res.addResult("average " + r.getName(), i, Pair.create(avg, stddev));
    }
    return res;
  }

  /**
   * Returns the experiment names for the given size.
   */
  public Set<String> getExperimentForSize(int size){
    Set<String> results = new LinkedHashSet<String>();
    for (String exp : getExperimentNames()){
      if (getSizes(exp).contains(size)){
        results.add(exp);
      }
    }
    return results;
  }

  /**
   * Merges two result sets.
   */
  public SolverExperimentResultSet<T> merge(SolverExperimentResultSet<T> that){
    SolverExperimentResultSet<T> res = new SolverExperimentResultSet<T>(this.getName() + " and " + that.getName());
    @SuppressWarnings("unchecked")
    Set<String> experims = CollectionsExt.union(this.getExperimentNames(), that.getExperimentNames());
    for (String experim : experims){
      for (int size : this.getSizes(experim)){
        res.addResult(experim, size, this.getResult(experim, size));
      }
      for (int size : that.getSizes(experim)){
        res.addResult(experim, size, that.getResult(experim, size));
      }
    }
    return res;
  }

  /**
   * SAT file contains, for each size and problem, 1 or 0 indicating SAT/UNSAT.
   * NOTE: works only for T = Pair<Boolean, Double>. TODO enforce this.
   */
  public String asSatFileContent(){
    StringBuilder s = new StringBuilder();
    int maxSize = maxSize();
    if (maxSize == -1)
      return "";
    assert maxSize >= 0 : maxSize;
    for (int size = minSize(); size <= maxSize; size++){
      s.append(size + " ");
      for (String name : new TreeSet<String>(getExperimentNames())){//sort experiments by name
        T result = getResult(name, size);
        assert result != null;
        assert result instanceof Pair;
        @SuppressWarnings("unchecked")
        Pair<Boolean, Double> p = (Pair<Boolean, Double>) result;
        s.append((p.first ? "1" : "0")).append(" ");
      }
      s.append(Utils.nl);
    }
    return s.toString();
  }
}
