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

import java.util.*;

/**
 * Maps each key to exactly 1 value, and vice versa.
 */
public class OneToOneMap<K, V> {
  private final Map<K, V> keyToValue;
  private final Map<V, K> valueToKey;

  public OneToOneMap(){
    keyToValue = new LinkedHashMap<K, V>();
    valueToKey = new LinkedHashMap<V, K>();
  }

  public void put(K k, V v){
    keyToValue.put(k, v);
    valueToKey.put(v, k);
  }

  public boolean containsK(K k){
    return keyToValue.containsKey(k);
  }

  public boolean containsV(V v){
    return valueToKey.containsKey(v);
  }

  public Set<K> getKs(){
    return keyToValue.keySet();
  }

  public Set<V> getVs(){
    return valueToKey.keySet();
  }

  public V getV(K k){
    return keyToValue.get(k);
  }

  public K getK(V v){
    return valueToKey.get(v);
  }

  public void clear(){
    keyToValue.clear();
    valueToKey.clear();
  }

  @Override
  public String toString(){
    StringBuilder b = new StringBuilder();
    b.append("{");
    for (K k : getKs()){
      b.append(k + "-" + getV(k) + ", ");
    }
    b.append("}");
    return b.toString();
  }

  /**
   * Returns the number of key-value pairs in this map.
   */
  public int size(){
    return keyToValue.size();
  }
}
