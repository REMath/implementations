/*
 * LazyTreeMap.java - This file is part of the Jakstab project.
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

/**
 * @author Johannes Kinder
 */
public class LazyTreeMap<K, V> extends AbstractMap<K, V> implements Map<K, V> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(LazyTreeMap.class);
	
	private class ReferenceCountingTreeMap<L, W> extends TreeMap<L, W> {
		private static final long serialVersionUID = -6043771577607149364L;
		private int referenceCount;
		private int hashCode = 0;
		
		public ReferenceCountingTreeMap() {
			super();
			referenceCount = 1;
		}

		public ReferenceCountingTreeMap(ReferenceCountingTreeMap<L, W> innerMap) {
			super(innerMap);
			referenceCount = 1;
		}
		
		public void addRef() {
			referenceCount++;
		}
		
		public void release() {
			referenceCount--;
		}
		
		public boolean isShared() {
			return referenceCount > 1;
		}
	}
	
	private ReferenceCountingTreeMap<K, V> innerMap;
	private transient Set<Map.Entry<K, V>> entries;
	
	public LazyTreeMap() {
		innerMap = new ReferenceCountingTreeMap<K, V>();
	}
	
	public LazyTreeMap(LazyTreeMap<K, V> other) {
		innerMap = other.innerMap;
		innerMap.addRef();
	}
	
	private boolean makeExclusive() {
		// makeExclsusive is called before all updates to inner map, 
		// so reset cached hashcode
		innerMap.hashCode = 0;
		
		if (innerMap.isShared()) {
			innerMap.release();
			innerMap = new ReferenceCountingTreeMap<K, V>(innerMap);
			assert !innerMap.isShared();
			return true;
		}
		return false;
	}
	
	@Override
	public void clear() {
		makeExclusive();
		innerMap.clear();
	}

	@Override
	public V get(Object key) {
		return innerMap.get(key);
	}

	@Override
	public V put(K key, V value) {
		makeExclusive();
		return innerMap.put(key, value);
	}

	@Override
	public V remove(Object key) {
		makeExclusive();
		return innerMap.remove(key);
	}

	@Override
	public int size() {
		return innerMap.size();
	}

	@Override
	public boolean containsKey(Object key) {
		return innerMap.containsKey(key);
	}

	@Override
	public boolean containsValue(Object value) {
		return innerMap.containsValue(value);
	}

	@Override
	public boolean equals(Object o) {
		LazyTreeMap<?, ?> other = (LazyTreeMap<?, ?>)o;
		return innerMap.equals(other.innerMap);
	}

	@Override
	public int hashCode() {
		if (innerMap.hashCode == 0)
			innerMap.hashCode = innerMap.hashCode();
		return innerMap.hashCode;
	}

	@Override
	public boolean isEmpty() {
		return innerMap.isEmpty();
	}

	@Override
	protected void finalize() throws Throwable {
		innerMap.release();
		super.finalize();
	}

	@Override
	public Set<Map.Entry<K, V>> entrySet() {
		if (entries == null)
			entries = new EntrySet();
		return entries;
	}

	private final class EntrySet extends AbstractSet<Map.Entry<K,V>> {
		@Override
		public Iterator<Map.Entry<K, V>> iterator() {
			return new MapEntryIterator();
		}

		@Override
		public boolean contains(Object o) {
			Map.Entry<?, ?> entry = (Map.Entry<?, ?>)o;
			V value = get(entry.getKey());
			if (value == null)
				return entry.getValue() == null;
			else
				return value.equals(entry.getValue());
		}

		@Override
		public int size() {
			return innerMap.size();
		}

	}
	
	private final class MapEntryIterator implements Iterator<Map.Entry<K,V>> {
		private Iterator<Map.Entry<K,V>> innerIt = 
			innerMap.entrySet().iterator();
		private Map.Entry<K, V> last = null;

		@Override
		public boolean hasNext() {
			return innerIt.hasNext();
		}

		@Override
		public Map.Entry<K, V> next() {
			last = innerIt.next();
			return last;
		}

		@Override
		public void remove() {
			if (makeExclusive()) {
				// yes, we copied the map, so refresh iterator
				innerIt = innerMap.entrySet().iterator();
				// fast forward to old position
				if (last != null) {
					while (!last.equals(innerIt.next()))
						assert innerIt.hasNext();
				}
			}
			innerIt.remove();
		}
	}

}
