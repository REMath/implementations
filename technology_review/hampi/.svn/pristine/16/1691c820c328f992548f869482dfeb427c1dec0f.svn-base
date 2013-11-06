/*******************************************************************************
 * The MIT License
 *
 * Copyright (c) 2008 Adam Kiezun
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ******************************************************************************/
package hampi.utils;

import java.lang.reflect.Array;
import java.util.*;
import java.util.Map.Entry;

public final class CollectionsExt{
  private CollectionsExt(){
    throw new IllegalStateException("no instances");
  }

  /**
   * Make a copy of the list with duplicates removed. The first elements of each
   * equivalence class will be retained (and in the original order)
   */
  public static <T> List<T> unique(List<T> lst){
    return new ArrayList<T>(new LinkedHashSet<T>(lst));
  }

  /**
   * Return a unmodifiable list that has all elements of the given collection.
   */
  public static <T> List<T> roCopyList(Collection<T> l){
    return Collections.unmodifiableList(new ArrayList<T>(l));
  }

  public static <T> Set<T> intersection(Set<? extends T>... sets){
    if (sets.length == 0)
      return Collections.emptySet();
    Set<T> result = new LinkedHashSet<T>();
    result.addAll(sets[0]);
    for (Set<? extends T> s : sets){
      result.retainAll(s);
    }
    return result;
  }

  public static <T> Set<T> intersectionSets(Set<Set<T>> sets){
    if (sets.isEmpty())
      return Collections.emptySet();
    Set<T> result = new LinkedHashSet<T>();
    result.addAll(sets.iterator().next());
    for (Set<? extends T> s : sets){
      result.retainAll(s);
    }
    return result;
  }

  @SuppressWarnings("unchecked")
  public static <T> Set<T> xor(Set<? extends T> s1, Set<? extends T> s2){
    return union(diff(s1, s2), diff(s2, s1));
  }

  public static <T> Set<T> diff(Set<? extends T> s1, Set<? extends T> s2){
    Set<T> result = new LinkedHashSet<T>();
    result.addAll(s1);
    result.removeAll(s2);
    return result;
  }

  public static <T> Set<T> union(Set<? extends T>... sets){
    Set<T> result = new LinkedHashSet<T>();
    for (Set<? extends T> s : sets){
      result.addAll(s);
    }
    return result;
  }

  public static <T> Set<T> unionS(Collection<Set<T>> sets){
    Set<T> result = new LinkedHashSet<T>();
    for (Set<? extends T> s : sets){
      result.addAll(s);
    }
    return result;
  }

  /**
   * Returns an ArrayList that is a concatenation of the arguments. Elements of
   * arguments are copied, the argument lists are NOT shared.
   */
  public static <T> List<T> concat(List<? extends T>... lists){
    List<T> result = new ArrayList<T>();
    for (List<? extends T> list : lists){
      result.addAll(list);
    }
    return result;
  }

  /**
   * Returns an ArrayList that is a concatenation of the arguments. Elements of
   * arguments are copied, the argument lists are NOT shared.
   */
  public static <T> List<T> concatAll(Collection<? extends List<? extends T>> lists){
    List<T> result = new ArrayList<T>();
    for (List<? extends T> list : lists){
      result.addAll(list);
    }
    return result;
  }

  public static <T> T getNthIteratedElement(Collection<? extends T> s, int index){
    if (s == null)
      throw new IllegalArgumentException("s cannot be null.");
    if (s.isEmpty())
      throw new IllegalArgumentException("s cannot be empty.");
    if (index >= s.size())
      throw new IllegalArgumentException("Index " + index + " invalid for set of size " + s.size());
    return getNthIteratedElement(s.iterator(), index);
  }

  public static <T> T getNthIteratedElement(Iterator<? extends T> iter, int index){
    if (index < 0)
      throw new IllegalArgumentException("Index " + index + " invalid");
    int counter = 0;
    for (Iterator<? extends T> i = iter; i.hasNext();){
      if (counter == index)
        return i.next();
      i.next();
      counter++;
    }
    throw new IllegalArgumentException("invalid index:" + index + " size:" + counter);
  }

  public static SortedSet<Integer> findAll(List<?> list, Object elem){
    if (list == null)
      throw new IllegalArgumentException("list cannot be null.");
    SortedSet<Integer> result = new TreeSet<Integer>();
    for (int i = 0, n = list.size(); i < n; i++){
      if (list.get(i).equals(elem)){
        result.add(i);
      }
    }

    return Collections.unmodifiableSortedSet(result);
  }

  /**
   * Prints out the String.valueOf() of all elements of the collection,
   * inserting a new line after each element. The order is specified by the
   * collection's iterator.
   */
  public static String toStringInLines(Collection<?> c){
    if (c.isEmpty())
      return "";
    return join(Utils.newLine, toStringLines(c)) + Utils.newLine;
  }

  /**
   * Prints out the elements of the collection in lines, in lexicographic order
   * of String.valueOf called on each element.
   */
  public static String toStringInSortedLines(Collection<?> c){
    if (c.isEmpty())
      return "";
    return join(Utils.newLine, sort(toStringLines(c))) + Utils.newLine;
  }

  /**
   * Prints out the elements of the collection in lines, in lexicographic order
   * of String.valueOf called on each element.
   */
  public static String toStringInSortedOneLine(Collection<?> c){
    if (c.isEmpty())
      return "";
    return join(" ", sort(toStringLines(c))) + Utils.newLine;
  }

  /**
   * List of String.valueOf() of all elements of the collection. The order is
   * specified by the collection's iterator.
   */
  public static List<String> toStringLines(Collection<?> c){
    List<String> lines = new ArrayList<String>(c.size());
    for (Object each : c){
      lines.add(String.valueOf(each));
    }
    return lines;
  }

  /**
   * Sort and return the list. Useful for chaining the call.
   */
  public static List<String> sort(List<String> strings){
    Collections.sort(strings);
    return strings;
  }

  /**
   * Divides the argument into chunks of at most the given length. All chunks
   * except at most one will have length exactly maxLength. No chunks are empty.
   *
   * The result list is unmodifiable. It does <em>not</em> copy the list and
   * simply shares it.
   */
  public static <T> List<List<T>> chunkUp(List<T> list, int maxLength){
    if (maxLength <= 0)
      throw new IllegalArgumentException("maxLength must be > 0 but was " + maxLength);
    int fullChunks = list.size() / maxLength;

    List<List<T>> result = new ArrayList<List<T>>(fullChunks + 1);
    for (int i = 0; i < fullChunks; i++){
      List<T> subList = list.subList(i * maxLength, (i + 1) * maxLength);
      if (subList.size() != maxLength)
        throw new IllegalStateException("bogus length:" + subList.size() + " not " + maxLength);
      result.add(subList);
    }
    List<T> lastChunk = list.subList(fullChunks * maxLength, list.size());
    if (!lastChunk.isEmpty()){
      result.add(lastChunk);
    }
    return Collections.unmodifiableList(result);
  }

  public static <T> Set<T> getAll(Enumeration<T> e){
    Set<T> result = new LinkedHashSet<T>();
    while (e.hasMoreElements()){
      result.add(e.nextElement());
    }
    return result;
  }

  /**
   * Removed from the collection all strings that match the given pattern.
   * Returns the modified collection, for easier chaining.
   */
  public static <T extends Collection<String>> T removeMatching(String pattern, T strings){
    for (Iterator<String> iter = strings.iterator(); iter.hasNext();){
      String s = iter.next();
      if (s.matches(pattern)){
        iter.remove();
      }
    }
    return strings;
  }

  /**
   * Reverse of String.split. Glues together the strings and inserts the
   * separator between each consecutive pair.
   */
  public static String join(String separator, List<String> strings){
    StringBuilder sb = new StringBuilder();
    for (Iterator<String> iter = strings.iterator(); iter.hasNext();){
      String s = iter.next();
      sb.append(s);
      if (iter.hasNext()){
        sb.append(separator);
      }
    }
    return sb.toString();
  }

  /**
   * Reverse of String.split. Glues together the strings and inserts the
   * separator between each consecutive pair.
   */
  public static String join(String separator, String[] args){
    return join(separator, Arrays.asList(args));
  }

  /**
   * Adds prefix to each line.
   */
  public static List<String> prefix(String prefix, List<String> lines){
    List<String> result = new ArrayList<String>(lines.size());
    for (String line : lines){
      result.add(prefix + line);
    }
    return result;
  }

  /**
   * Returns whether the sets are disjoint.
   *
   * XXX bogus for empty sets
   */
  public static boolean areDisjoint(Set<?>... ss){
    if (ss == null || ss.length == 0)
      return true;
    int elementCount = 0;
    for (Set<?> set : ss){
      elementCount += set.size();
    }
    return CollectionsExt.union(ss).size() == elementCount;
  }

  /**
   * Creates a set of all sequences of length max of objects. The order matters
   * and elements may be repeated. The set is grouped by the number of objects
   * in the array. The result is a map from arities to object sequences.
   *
   * NOTE: This is done with arrays rather than lists because in JOE we don't
   * want to execute any code of the objects.
   */
  public static Map<Integer, Set<Object[]>> createPerArityGroups(Object[] objects, int max){
    Map<Integer, Set<Object[]>> result = new LinkedHashMap<Integer, Set<Object[]>>();
    result.put(0, Collections.singleton(new Object[0]));
    for (int i = 1; i <= max; i++){
      Set<Object[]> newSet = new LinkedHashSet<Object[]>();
      // add each object to each one smaller
      for (Object[] oneSmaller : result.get(i - 1)){
        for (Object object : objects){
          newSet.add(CollectionsExt.addToArray(oneSmaller, object));
        }
      }
      result.put(i, newSet);
    }
    return result;
  }

  /**
   * Creates and returns an array that contains all elements of the array
   * parameter and has the el parameter appened.
   *
   * The runtime type of the resulting array is the same as the type of the
   * argument array.
   */
  @SuppressWarnings("unchecked")
  // nothing we can do here, we must cast
  public static <T> T[] addToArray(T[] array, T el){
    T[] newArray = (T[]) Array.newInstance(array.getClass().getComponentType(), array.length + 1);
    System.arraycopy(array, 0, newArray, 0, array.length);
    newArray[array.length] = el;
    return newArray;
  }

  /**
   * Returns whether all objects are instances of a given class.
   */
  public static boolean allInstancesOf(Class<?> clazz, Object[] objs){
    for (Object obj : objs){
      if (!clazz.isInstance(obj))
        return false;
    }
    return true;
  }

  /**
   * For a given list of list of objects, create and return the (exponential in
   * size) list of list of objects that comes from combining the every element
   * from the first list with every element from the second list etc. Eg for
   * input [[1,2],[a,b]] this returns [[1,a][1,b],[2,a],[2,b]]
   *
   * For empty input, returns a list with one element: empty list. Requires: all
   * lists non-empty
   */
  public static <T> List<List<T>> allCombinations(List<List<T>> inputs){
    if (inputs.isEmpty()){
      ArrayList<List<T>> result = new ArrayList<List<T>>(1);
      result.add(new ArrayList<T>(1));
      return result;
    }
    List<T> lastList = inputs.get(inputs.size() - 1);

    List<List<T>> result = new ArrayList<List<T>>();
    for (int i = 0; i < lastList.size(); i++){
      List<List<T>> tails = allCombinations(inputs.subList(0, inputs.size() - 1));
      T x = lastList.get(i);
      for (List<T> tail : tails){
        tail.add(x);
      }
      result.addAll(tails);
    }
    return result;
  }

  public static <K, V> Set<K> mappedTo(Map<K, V> map, V value){
    Set<K> result = new LinkedHashSet<K>();
    for (Entry<K, V> e : map.entrySet()){
      if (e.getValue().equals(value)){
        result.add(e.getKey());
      }
    }
    return result;
  }

  public static <T> Set<Set<T>> allSubsets(Set<T> set){
    if (set.isEmpty()){
      Set<Set<T>> r = new LinkedHashSet<Set<T>>();
      r.add(new LinkedHashSet<T>());
      return r;
    }
    T one = set.iterator().next();

    Set<Set<T>> result = new LinkedHashSet<Set<T>>();
    Set<Set<T>> allSubsets = allSubsets(oneLess(set, one));
    for (Set<T> subset : allSubsets){
      result.add(subset);
      result.add(oneMore(subset, one));
    }
    return result;
  }

  @SuppressWarnings("unchecked")
  public static <T> Set<T> oneMore(Set<T> set, T one){
    return CollectionsExt.union(set, Collections.singleton(one));
  }

  public static <T> Set<T> oneLess(Set<T> set, T one){
    return CollectionsExt.diff(set, Collections.singleton(one));
  }

  public static <T> Set<Set<T>> chooseAll(Set<T> set, int choose){
    if (choose < 0)
      throw new IllegalArgumentException("negative arg");
    if (choose > set.size())
      throw new IllegalArgumentException("cannot choose " + choose + " from a set of size " + set.size());
    if (choose == 0){
      LinkedHashSet<Set<T>> s = new LinkedHashSet<Set<T>>();
      s.add(new LinkedHashSet<T>());
      return s;
    }
    Set<Set<T>> result = new LinkedHashSet<Set<T>>();
    for (Set<T> nMinus1 : chooseAll(set, choose - 1)){
      for (T missing : CollectionsExt.diff(set, nMinus1)){
        result.add(oneMore(nMinus1, missing));
      }
    }
    // TODO Auto-generated method stub
    return result;
  }

  /**
   * Returns the lowest index of the element in the array or -1 if cannot be
   * found. Elements are compared by equality.
   */
  public static <T> int indexOf(T[] arr, T elem){
    for (int i = 0; i < arr.length; i++){
      T t = arr[i];
      if (elem == null && t == null)
        return i;
      if (elem != null && elem.equals(t))
        return i;
    }
    return -1;
  }

  public static <T> int[] indicesOf(T[] arr, Set<T> elems){
    Set<Integer> indices = new LinkedHashSet<Integer>();
    for (T t : elems){
      indices.add(indexOf(arr, t));
    }
    return toIntArray(indices);
  }

  public static int[] toIntArray(Collection<Integer> ints){
    int[] result = new int[ints.size()];
    int i = 0;
    for (int idx : ints){
      result[i++] = idx;
    }
    return result;
  }

  public static double[] toDoubleArray(Collection<Double> indices){
    double[] result = new double[indices.size()];
    int i = 0;
    for (double idx : indices){
      result[i++] = idx;
    }
    return result;
  }

  /**
   * Returns the list of pairs of <lower, upper> inclusive end of characters
   * ranges.
   */
  public static List<Pair<Character, Character>> ranges(char[] chars){
    assert chars != null;
    if (chars.length == 0)
      return Collections.emptyList();
    Arrays.sort(chars);
    if (chars.length == 1)
      return Collections.singletonList(Pair.create(chars[0], chars[0]));
    List<Integer> rangeEnds = new ArrayList<Integer>();
    for (int i = 1; i < chars.length; i++){
      if (chars[i - 1] + 1 != chars[i]){
        rangeEnds.add(i - 1);
      }
      if (i == chars.length - 1){
        rangeEnds.add(i);
      }
    }
    List<Pair<Character, Character>> result = new ArrayList<Pair<Character, Character>>();
    for (int i = 0; i < rangeEnds.size(); i++){
      char low;
      char high;
      if (i == 0){
        low = chars[0];
      }else{
        low = chars[rangeEnds.get(i - 1) + 1];
      }
      high = chars[rangeEnds.get(i)];
      result.add(Pair.create(low, high));
    }
    return result;
  }

  /**
   * Returns the mean of the numbers. Assumes the sum does not overflow.
   */
  public static double mean(long[] times){
    assert times != null && times.length > 0;
    return (sum(times) * 1.0) / times.length;
  }

  /**
   * Returns the mean of the numbers. Assumes the sum does not overflow.
   */
  public static Double mean(Collection<Double> times){
    assert times != null && times.size() > 0;
    return (sum(times) * 1.0) / times.size();
  }

  private static double mean(double[] data){
    assert data != null && data.length > 0;
    return (sum(data) * 1.0) / data.length;
  }

  public static double meanInts(Collection<Integer> sizes){
    assert sizes != null && sizes.size() > 0;
    return (sumInts(sizes) * 1.0) / sizes.size();
  }

  public static int sumInts(Collection<Integer> sizes){
    int res = 0;
    for (int s : sizes){
      res += s;
    }
    return res;
  }

  /**
   * Returns the sum of the numbers. May overflow.
   */
  public static double sum(Collection<Double> times){
    double res = 0;
    for (Double d : times){
      res += d;
    }
    return res;
  }

  public static double sum(double[] data){
    double sum = 0;
    for (double l : data){
      sum += l;
    }
    return sum;
  }

  /**
   * Returns the sum of the numbers. May overflow.
   */
  public static long sum(long[] times){
    long sum = 0;
    for (long l : times){
      sum += l;
    }
    return sum;
  }

  /**
   * Creates an new array that holds n elements of arr, starting at idx.
   */
  public static String[] subarray(String[] arr, int idx, int n){
    String[] res = new String[n];
    System.arraycopy(arr, idx, res, 0, n);
    return res;
  }

  /**
   * Calculates the standard deviation of an array of numbers. see Knuth's The
   * Art Of Computer Programming Volume II: Seminumerical Algorithms This
   * algorithm is slower, but more resistant to error propagation.
   *
   * The 'sample' parameter denotes whether this is the estimate of the sample.
   */
  private static double stddev(int[] data, boolean sample){
    final int n = data.length;
    if (n < 2)
      return 0;
    double avg = data[0];
    double sum = 0;
    for (int i = 1; i < data.length; i++){
      double newavg = avg + (data[i] - avg) / (i + 1);
      sum += (data[i] - avg) * (data[i] - newavg);
      avg = newavg;
    }
    if (sample)
      return Math.sqrt(sum / n);
    else
      return Math.sqrt(sum / (n - 1));
  }

  /**
   * Calculates the standard deviation of an array of numbers. see Knuth's The
   * Art Of Computer Programming Volume II: Seminumerical Algorithms This
   * algorithm is slower, but more resistant to error propagation.
   *
   * The 'sample' parameter denotes whether this is the estimate of the sample.
   */
  public static double stddev(double[] data, boolean sample){
    final int n = data.length;
    if (n < 2)
      return 0;
    double avg = data[0];
    double sum = 0;
    for (int i = 1; i < data.length; i++){
      double newavg = avg + (data[i] - avg) / (i + 1);
      sum += (data[i] - avg) * (data[i] - newavg);
      avg = newavg;
    }
    if (sample)
      return Math.sqrt(sum / n);
    else
      return Math.sqrt(sum / (n - 1));
  }

  /**
   * Computed the standard deviation of the set of numbers. The 'sample'
   * parameter denotes whether this is the estimate of the sample.
   */
  public static Double stddev(Set<Double> times, boolean sample){
    double res = stddev(toDoubleArray(times), sample);
    return res;
  }

  /**
   * Computed the standard deviation of the set of numbers. The 'sample'
   * parameter denotes whether this is the estimate of the sample.
   */
  public static Double stddevInts(Collection<Integer> sizes, boolean sample){
    double res = stddev(toIntArray(sizes), sample);
    return res;
  }

  /**
   * Repeats the t element n times.
   */
  public static <T> List<T> repeat(T t, int n){
    assert n >= 0;
    List<T> result = new ArrayList<T>(n);
    for (int i = 0; i < n; i++){
      result.add(t);
    }
    return result;
  }

}
