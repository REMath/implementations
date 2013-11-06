package hampi.utils;

public final class StopWatch{

  private final String name;
  private long         total        = 0;
  private long         lastStart    = 0;
  private int          timesStarted = 0;
  private int stackHeight = 0;//we allow nested starts
  private final Histogram<Long> times = new Histogram<Long>();

  public StopWatch(String name){
    this.name = name;
  }

  public void start(){
    if (stackHeight == 0){
      lastStart = System.currentTimeMillis();
      timesStarted++;
    }
    stackHeight++;
  }

  public void stop(){
    stackHeight--;
    if (stackHeight == 0){
      if (lastStart == 0)
        throw new IllegalStateException("not started");
      long now = System.currentTimeMillis();
      long time = now - lastStart;
      times.put(time);
      total += time;
      lastStart = 0;
    }
  }

  public String getName(){
    return name;
  }

  public long getTotal(){
    return total;
  }

  @Override
  public String toString(){
    String stillRunning = lastStart != 0 ? " [running]" : "";
    return name + ": " + total + "ms " + "(" + timesStarted + " times" + ")" + stillRunning;
  }

  public Histogram<Long> getTimesHistogram(){
    return times;
  }

  public int getCount(){
    return timesStarted;
  }
}
