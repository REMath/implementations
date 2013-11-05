/*
 * LazyHashMapMap.java - This file is part of the Jakstab project.
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
 * HashMapMap with lazy copying. I.e., only copies submaps if they are modified.
 * 
 * @author Johannes Kinder
 */
public final class LazyHashMapMap<K, L, V> implements MapMap<K,L,V> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(LazyHashMapMap.class);

	private static final class ReferenceCountingHashMapMap<M, N, W> extends HashMapMap<M, N, W> {

		private int referenceCount;
		private int hashCode = 0;
		
		public ReferenceCountingHashMapMap() {
			super();
			referenceCount = 1;
		}

		public ReferenceCountingHashMapMap(
				ReferenceCountingHashMapMap<M, N, W> innerMap) {
			super(innerMap);
			referenceCount = 1;
		}
		
		protected Map<N, W> createSubMap() {
			return new LazyTreeMap<N, W>();
		}
		
		protected Map<N, W> createSubMap(Map<N, W> proto) {
			return new LazyTreeMap<N, W>((LazyTreeMap<N, W>)proto);
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
	
	public LazyHashMapMap() {
		this.innerMap = new ReferenceCountingHashMapMap<K, L, V>();
	}
	
	public LazyHashMapMap(LazyHashMapMap<K, L, V> proto) {
		this.innerMap = proto.innerMap;
		this.innerMap.addRef();
	}

	private ReferenceCountingHashMapMap<K, L, V> innerMap;

	public boolean makeExclusive() {
		if (innerMap.isShared()) {
			innerMap.release();
			innerMap = new ReferenceCountingHashMapMap<K, L, V>(innerMap);
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
	public boolean containsKey(K keyLeft, L keyRight) {
		return innerMap.containsKey(keyLeft, keyRight);
	}

	@Override
	public boolean containsLeftKey(K keyLeft) {
		return innerMap.containsLeftKey(keyLeft);
	}

	@Override
	public V get(K keyLeft, L keyRight) {
		return innerMap.get(keyLeft, keyRight);
	}

	@Override
	public Map<L, V> getSubMap(K keyLeft) {
		Map<L, V> subMap = innerMap.getSubMap(keyLeft);
		if (subMap == null) return null;
		//return subMap;
		return Collections.unmodifiableMap(subMap);
	}
	
	public Iterator<Map.Entry<L, V>> subMapIterator(K keyLeft) {
		Map<L, V> subMap;
		if (innerMap.containsLeftKey(keyLeft)) {
			// Required, the caller might call remove on the iterator and
			// we would not notice the modification
			makeExclusive();
			// subMap is now already from the copy
			subMap = innerMap.getSubMap(keyLeft);
		} else {
			subMap = Collections.emptyMap();
		}
		return subMap.entrySet().iterator();
	}

	@Override
	public boolean isEmpty() {
		return innerMap.isEmpty();
	}

	@Override
	public Set<K> leftKeySet() {
		return innerMap.leftKeySet();
	}

	@Override
	public V put(K keyLeft, L keyRight, V value) {
		makeExclusive();
		return innerMap.put(keyLeft, keyRight, value);
	}

	@Override
	public void putAll(MapMap<K, L, V> other) {
		makeExclusive();
		innerMap.putAll(other);
	}

	@Override
	public V remove(K keyLeft, L keyRight) {
		makeExclusive();
		return innerMap.remove(keyLeft, keyRight);
	}

	@Override
	public void remove(K keyLeft) {
		makeExclusive();
		innerMap.remove(keyLeft);
	}

	@Override
	public int size() {
		return innerMap.size();
	}

	@Override
	public boolean equals(Object obj) {
		return innerMap.equals(((LazyHashMapMap<?,?,?>)obj).innerMap);
	}

	@Override
	public int hashCode() {
		if (innerMap.hashCode == 0)
			innerMap.hashCode = innerMap.hashCode();
		return innerMap.hashCode;
	}

	@Override
	public String toString() {
		return innerMap.toString();
	}

	@Override
	protected void finalize() throws Throwable {
		innerMap.release();
		super.finalize();
	}

	@Override
	public EntryIterator<K, L, V> entryIterator() {
		return innerMap.entryIterator();
	}
}
