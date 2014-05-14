/*
 * HashMapMap.java - This file is part of the Jakstab project.
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, see <http://www.gnu.org/licenses/>.
 */
package org.jakstab.util;

import java.util.*;

import org.jakstab.util.Logger;

public class HashMapMap<K, L, V> implements MapMap<K, L, V> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(HashMapMap.class);
	
	private Map<K, Map<L,V>> map;
	
	protected Map<L, V> createSubMap() {
		return new TreeMap<L, V>();
	}
	
	protected Map<L, V> createSubMap(Map<L, V> proto) {
		return new TreeMap<L, V>(proto);
	}
	
	public HashMapMap() {
		map = new HashMap<K, Map<L, V>>();
	}
	
	public HashMapMap(MapMap<K, L, V> proto) {
		this();
		for (K key : proto.leftKeySet()) {
			map.put(key, createSubMap(proto.getSubMap(key)));
		}
	}

	public boolean containsKey(K keyLeft, L keyRight) {
		if (map.containsKey(keyLeft)) 
			return map.get(keyLeft).containsKey(keyRight);
		else return false;
	}

	public boolean containsLeftKey(K keyLeft) {
		return map.containsKey(keyLeft); 
	}

	@Override
	public V get(K keyLeft, L keyRight) {
		Map<L, V> subMap = map.get(keyLeft);
		if (subMap != null) return subMap.get(keyRight);
		else return null;
	}

	@Override
	public V put(K keyLeft, L keyRight, V value) {
		Map<L, V> subMap = map.get(keyLeft);
		if (subMap == null) {
			subMap = createSubMap();
			map.put(keyLeft, subMap);
		}
		V oldValue = subMap.put(keyRight, value);
		return oldValue;
	}

	@Override
	public void putAll(MapMap<K, L, V> other) {
		for (EntryIterator<K, L, V> it = entryIterator(); it.hasEntry(); it.next()) {
			put(it.getLeftKey(), it.getRightKey(), it.getValue());
		}
	}

	@Override
	public V remove(K keyLeft, L keyRight) {
		Map<L, V> subMap = map.get(keyLeft);
		if (subMap != null) {
			V oldValue = subMap.remove(keyRight);
			if (subMap.isEmpty()) map.remove(keyLeft);
			return oldValue;
		}
		else return null;
	}
	
	@Override
	public void remove(K keyLeft) {
		map.remove(keyLeft);
	}

	@Override
	public Map<L, V> getSubMap(K keyLeft) {
		return map.get(keyLeft);
	}

	@Override
	public void clear() {
		map.clear();
	}
	
	@Override
	public Set<K> leftKeySet() {
		return map.keySet();
	}
	
	@Override
	public EntryIterator<K, L, V> entryIterator() {
		return new DoubleIterator();
	}
	
	private final class DoubleIterator implements EntryIterator<K, L, V> {
		private Iterator<K> it1;
		private K currentLeftKey;
		private Map.Entry<L, V> currentSubMapEntry; 
		private Iterator<Map.Entry<L, V>> it2;
		
		public DoubleIterator() {
			if (map.isEmpty()) {
				it1 = null;
				it2 = null;
				currentLeftKey = null;
				currentSubMapEntry = null;
			} else {
				it1 = map.keySet().iterator();
				currentLeftKey = it1.next();
				it2 = map.get(currentLeftKey).entrySet().iterator();
				next();
			}
		}
		
		@Override
		public K getLeftKey() {
			return currentLeftKey;
		}

		@Override
		public L getRightKey() {
			return currentSubMapEntry.getKey();
		}

		@Override
		public V getValue() {
			return currentSubMapEntry.getValue();
		}

		@Override
		public boolean hasEntry() {
			return (currentLeftKey != null);
		}

		@Override
		public void next() {
			
			if (!hasEntry()) throw new NoSuchElementException();

			// If it2 has no next element, iterate it1 as long
			// as we find a map that has elements
			while (!it2.hasNext()) {
				if (!it1.hasNext()) {
					currentSubMapEntry = null;
					currentLeftKey = null;
					return;
				}
				currentLeftKey = it1.next();
				it2 = map.get(currentLeftKey).entrySet().iterator();
			}
			currentSubMapEntry = it2.next();
		}
		
	}

	@Override
	public int size() {
		int res = 0;
		for (Map.Entry<K, Map<L, V>> subEntry : map.entrySet()) {
			res += subEntry.getValue().size();
		}
		return res;
	}

	@Override
	public boolean isEmpty() {
		return size() == 0;
	}

	@Override
	public int hashCode() {
		return map.hashCode();
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		HashMapMap<K, L, V> other = (HashMapMap<K, L, V>) obj;
		if (map == null) {
			return other.map == null;
		} else {
			// MapMaps are equal even if one has empty submaps which
			// the other does not have, so we cannot simply use equals()
			if (size() != other.size()) return false;
			// Check equality of submaps only one way - if this one lacks some
			// maps of the other, sizes will be different
			for (K leftKey : leftKeySet()) {
				Map<L,V> otherSubMap = other.getSubMap(leftKey);
				if (otherSubMap == null) {
					if (!getSubMap(leftKey).isEmpty())
						return false;
					// else getSubMap is empty and otherSubMap == null, so check next submap
				} else {
					if (!otherSubMap.equals(getSubMap(leftKey)))
						return false;
				}
			}
			return true;
		}
			
	}

}
