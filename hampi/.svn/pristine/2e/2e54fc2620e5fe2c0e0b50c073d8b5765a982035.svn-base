package hampi.utils;

import java.io.Serializable;
import java.util.*;
import java.util.Map.Entry;

/**
 * Keeps track of how many objects of different kinds are inserted into it.
 */
public final class Histogram<T> implements Serializable{
  private static final long     serialVersionUID = 7401396200080635154L;
  private final Map<T, Integer> map              = new LinkedHashMap<T, Integer>();
  private String                name;

  public Histogram(String name){
    this.name = name;
  }

  public Histogram(){
    this(null);
  }

  public void put(T t){
    put(t, 1);
  }

  public void setName(String name){
    this.name = name;
  }

  public String getName(){
    return name;
  }

  public void put(T t, int k){
    if (k < 0)
      throw new IllegalArgumentException("k:" + k);
    if (!map.containsKey(t)){
      map.put(t, k);
    }else{
      map.put(t, getCount(t) + k);
    }
  }

  @Override
  public String toString(){
    return toStringSortedByKey();
  }

  public String toStringSortedByNumbers(){
    return entriesToString(true, new Comparator<Map.Entry<T, Integer>>(){
      public int compare(Map.Entry<T, Integer> e1, Map.Entry<T, Integer> e2){
        Integer value1 = e1.getValue();
        Integer value2 = e2.getValue();
        return value2.intValue() - value1.intValue();
      }
    });
  }

  /**
   * Note: This works only when keys are comparable.
   */
  public String toStringSortedByKey(){
    return entriesToString(true, new Comparator<Map.Entry<T, Integer>>(){
      @SuppressWarnings("unchecked")
      public int compare(Map.Entry<T, Integer> e1, Map.Entry<T, Integer> e2){
        Comparable key1 = (Comparable) e1.getKey();
        Comparable key2 = (Comparable) e2.getKey();
        return key1.compareTo(key2);
      }
    });
  }

  private String entriesToString(boolean append_percent, Comparator<Map.Entry<T, Integer>> c){
    List<Map.Entry<T, Integer>> entries = new ArrayList<Map.Entry<T, Integer>>(map.entrySet());
    Collections.sort(entries, c);
    StringBuilder sb = new StringBuilder();
    if (this.name != null){
      sb.append("Histogram:").append(this.name).append("\n");
    }
    int size = getSize();
    sb.append("Total size:" + size).append("\n");
    for (Entry<T, Integer> e : entries){
      sb.append(Utils.rpad(e.getValue(), 9));
      if (append_percent){
        sb.append(Utils.rpad(createPercentString(size, e), 8));
      }
      sb.append(e.getKey() + "\n");
    }
    return sb.toString();
  }

  private String createPercentString(int size, Map.Entry<T, Integer> e){
    float size_f = size;//this this assignment for conversion
    float count = getCount(e.getKey());//this assignment for conversion
    int percent = Math.round((count / size_f) * 100);
    return " [" + percent + "%]";
  }

  private int getSize(){
    int result = 0;
    for (T t : map.keySet()){
      result += getCount(t);
    }
    return result;
  }

  public int getCount(T t){
    if (map.containsKey(t))
      return map.get(t);
    else
      return 0;
  }

  public void clear(){
    map.clear();
  }

  /**
   * Returns the total count of all elements.
   */
  public int totalCount(){
    int total = 0;
    for (T key : keySet()){
      total += getCount(key);
    }
    return total;
  }

    public Set<T> keySet(){
    return map.keySet();
  }

    /**
   * Returns the maximum count.
   */
  public int getMaxCount(){
    int max = Integer.MIN_VALUE;
    for (T key : keySet()){
      max = Math.max(max, getCount(key));
    }
    return max;
  }

  /**
   * Returns the mean of the results.
   */
  public static double mean(Histogram<Integer> h){
    int sum = sum(h);
    int size = h.getSize();
    return (sum * 1.0) / size;
  }

  /**
   * Returns the sum of the numbers. May overflow.
   */
  private static int sum(Histogram<Integer> h){
    int res = 0;
    for (int elem : h.keySet()){
      res += elem * h.getCount(elem);
    }
    return res;
  }
}
