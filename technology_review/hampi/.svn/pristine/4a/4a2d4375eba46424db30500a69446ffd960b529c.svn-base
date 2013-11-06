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

import java.math.BigInteger;
import java.util.*;

public final class Randomness{

  private Randomness(){
    // no instances
  }

  public static final long SEED   = 0;

  /**
   * The random number used any testtime a random choice is made. (Developer
   * note: do not declare new Random objects; use this one instead).
   */
  private static Random    random = new Random(SEED);

  public static Random getRandom(){
    return random;
  }

  public static void reset(long newSeed){
    random = new Random(newSeed);
  }

  public static int totalCallsToRandom = 0;

  public static boolean nextRandomBool(){
    totalCallsToRandom++;
    return random.nextBoolean();
  }

  public static String nextRandomString(int length){
    totalCallsToRandom++;
    byte[] bytes = new byte[length];
    random.nextBytes(bytes);
    return new String(bytes);
  }

  public static String nextRandomASCIIString(int length){
    char firstAscii = ' ';
    char lastAscii = '~';
    return nextRandomStringFromRange(length, firstAscii, lastAscii);
  }

  public static String nextRandomStringFromRange(int length, char min, char max){
    if (min > max)
      throw new IllegalArgumentException("max lower than min " + max + " " + min);
    totalCallsToRandom++;
    char[] chars = new char[length];
    for (int i = 0; i < chars.length; i++){
      chars[i] = (char) (min + random.nextInt(max - min + 1));
    }
    return new String(chars);
  }

  /**
   * Uniformly random int from [0, i)
   */
  public static int nextRandomInt(int i){
    totalCallsToRandom++;
    return random.nextInt(i);
  }

  /**
   * Uniformly random int from MIN to MAX
   */
  public static int nextRandomInt(){
    totalCallsToRandom++;
    return random.nextInt();
  }

  /**
   * Uniformly random int from [0, i)
   */
  public static long nextRandomLong(long i){
    totalCallsToRandom++;
    return Math.abs(random.nextLong()) % i;
  }

  public static <T> T randomMember(List<T> list){
    if (list == null || list.isEmpty())
      throw new IllegalArgumentException("Expected non-empty list");
    return list.get(nextRandomInt(list.size()));
  }

  public static <T> T randomSetMember(Collection<T> set){
    int randIndex = Randomness.nextRandomInt(set.size());
    return CollectionsExt.getNthIteratedElement(set, randIndex);
  }

  public static boolean randomBoolFromDistribution(double falseProb_, double trueProb_){
    totalCallsToRandom++;
    double falseProb = falseProb_ / (falseProb_ + trueProb_);
    return Randomness.random.nextDouble() >= falseProb;
  }

  // TODO Should be made more efficient
  public static <T> Set<T> randomNonEmptySubset(Set<T> set){
    Set<T> copy = new LinkedHashSet<T>(set);
    int i = nextRandomInt(set.size()) + 1;
    Set<T> result = new LinkedHashSet<T>(i);
    for (; i > 0; i--){
      T randomSetMember = randomSetMember(copy);
      result.add(randomSetMember);
      copy.remove(randomSetMember);
    }
    return result;
  }

  /**
   * Given array [x_i] select the index k with a probability x_k / sum(x_i)
   */
  public static int choose(BigInteger[] lst){
    BigInteger sum = Randomness.sum(lst);
    if (sum.compareTo(BigInteger.ZERO) <= 0)
      throw new IllegalArgumentException("bad distribution " + Arrays.toString(lst));
    BigInteger randomLong = nextRandomBigInteger(sum).add(BigInteger.ONE);
    BigInteger acc = BigInteger.ZERO;
    for (int i = 0; i < lst.length; i++){
      acc = acc.add(lst[i]);
      if (lst[i].compareTo(BigInteger.ZERO) < 0)
        throw new IllegalStateException("negative count:" + Arrays.toString(lst));
      if (acc.compareTo(randomLong) >= 0){
        if (lst[i].compareTo(BigInteger.ZERO) <= 0)
          throw new IllegalStateException("zero probability");
        return i;
      }
    }
    throw new IllegalStateException("should not reach here:" + Arrays.toString(lst) + " sum:" + sum + " acc:" + acc + " rand:" + randomLong);
  }

  public static BigInteger nextRandomBigInteger(BigInteger max){
    return new BigInteger(max.bitLength(), random).mod(max);
  }

  public static BigInteger sum(BigInteger[] array){
    BigInteger result = BigInteger.ZERO;
    for (BigInteger i : array){
      result = result.add(i);//+= i;
    }
    return result;
  }

  public static String nextRandomString(int size, char... alphabet){
    char[] chs = new char[size];
    for (int i = 0; i < chs.length; i++){
      int randIdx = Randomness.nextRandomInt(alphabet.length);
      chs[i] = alphabet[randIdx];
    }
    return new String(chs);
  }
}
