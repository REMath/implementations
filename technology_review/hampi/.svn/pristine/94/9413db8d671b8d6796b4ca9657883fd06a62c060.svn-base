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

import java.io.Serializable;
import java.util.*;

/**
 * Map indexed with 2 keys.
 */
public final class DoubleKeyMap<K1, K2, V> implements Serializable{

  private static final long         serialVersionUID = 986549299527072961L;
  private final Map<K1, Map<K2, V>> fMap;

  public DoubleKeyMap(){
    fMap = new LinkedHashMap<K1, Map<K2, V>>();
  }

  public Set<K1> getK1Set(){
    return Collections.unmodifiableSet(fMap.keySet());
  }

  public Set<K2> getK2Set(K1 k1){
    return Collections.unmodifiableSet(getSecondLevel(k1).keySet());
  }

  public Set<V> getVSet(K1 k1){
    return Collections.unmodifiableSet(new LinkedHashSet<V>(getSecondLevel(k1).values()));
  }

  private Map<K2, V> getSecondLevel(K1 k1){
    if (fMap.containsKey(k1))
      return fMap.get(k1);
    else
      return Collections.emptyMap();
  }

  public boolean containsKeys(K1 k1, K2 k2){
    Map<K2, V> secondLevel = fMap.get(k1);//get directly, for speed
    if (secondLevel == null)
      return false;
    else
      return secondLevel.containsKey(k2);
  }

  public V get(K1 k1, K2 k2){
    Map<K2, V> secondLevel = fMap.get(k1);//get directly, for speed
    if (secondLevel == null)
      return null;
    return secondLevel.get(k2);
  }

  public V put(K1 k1, K2 k2, V v){
    Map<K2, V> secLvl = fMap.get(k1);//get directly, for speed
    if (secLvl == null){
      secLvl = new LinkedHashMap<K2, V>(2);
      fMap.put(k1, secLvl);
    }
    V oldV = secLvl.put(k2, v);
    return oldV;
  }

  @Override
  public String toString(){
    StringBuilder b = new StringBuilder();
    for (K1 k1 : fMap.keySet()){
      Map<K2, V> map = fMap.get(k1);
      for (K2 k2 : map.keySet()){
        b.append("[" + k1 + " " + k2 + "]->" + map.get(k2) + "\n");
      }
    }
    return b.toString();
  }

  public void clear(){
    fMap.clear();
  }

  public Set<V> getAllVs(){
    Set<V> result = new LinkedHashSet<V>();
    Set<K1> k1Set = getK1Set();
    for (K1 k1 : k1Set){
      result.addAll(getVSet(k1));
    }
    return Collections.unmodifiableSet(result);
  }

  public void remove(K1 key){
    fMap.remove(key);
  }

  public void remove2(K2 key){
    fMap.values().remove(key);

  }

  /**
   * Returns the number of triples.
   */
  public int size(){
    int result = 0;
    for (K1 k1 : getK1Set()){
      for (K2 k2 : getK2Set(k1)){
        if (containsKeys(k1, k2)){
          result++;
        }
      }
    }
    return result;
  }

  /**
   * Returns the set of all pairs of arguments.
   */
  public Set<Pair<K1, K2>> getK1K2Pairs(){
    Set<Pair<K1, K2>> result = new LinkedHashSet<Pair<K1, K2>>();
    for (K1 k1 : getK1Set()){
      for (K2 k2 : getK2Set(k1)){
        result.add(Pair.create(k1, k2));
      }
    }
    return result;
  }

  public boolean isEmpty(){
    return fMap.isEmpty();
  }
}
