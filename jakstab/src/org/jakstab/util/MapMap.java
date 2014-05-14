/*
 * MapMap.java - This file is part of the Jakstab project.
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

import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * A set of triples, follows several conventions from the Collections API.
 * 
 * @author Johannes Kinder
 * @param <K> Type of left keys.
 * @param <L> Type of right keys.
 * @param <V> Type of values
 */
public interface MapMap<K, L, V> {
	
	public V get(K keyLeft, L keyRight);

	public V put(K keyLeft, L keyRight, V value);
	
	public void putAll(MapMap<K, L, V> other);
	
	public boolean containsKey(K keyLeft, L keyRight);

	public boolean containsLeftKey(K keyLeft);
	
	public V remove(K keyLeft, L keyRight);
	
	/**
	 * Removes all triples with the specified left key from this map.
	 * 
	 * @param keyLeft the left key for which all triples should be removed.
	 */
	public void remove(K keyLeft);
	
	public Map<L, V> getSubMap(K keyLeft);
	
	/**
	 * Returns the number of triples in this map by adding the sizes
	 * of all submaps.
	 * 
	 * @return the number of triples in this map.
	 */
	public int size();
	
	public void clear();
	
	public boolean isEmpty();
	
	public Set<K> leftKeySet();

	public EntryIterator<K, L, V> entryIterator();
	
	/**
	 * An iterator for MapMaps that behaves differently from regular
	 * iterators. Provides direct accessor methods for the current entry
	 * to avoid object creation.
	 */
	public static interface EntryIterator<K, L, V>
	{
		/**
		 * Move the current entry to the next.
		 * 
		 * @throws NoSuchElementException if there is no current entry and we
		 *         it move past the end. 
		 */
		public void next();
		
		/**
		 * Check whether the iterator has reached the end.
		 * 
		 * @return True if the current entry is valid, false if the iteration
		 *         has reached the end and the current entry is invalid.
		 */
		public boolean hasEntry();
		
		/**
		 * @return the left key of the current entry
		 */
		public K getLeftKey();

		/**
		 * @return the right key of the current entry
		 */
		public L getRightKey();

		/**
		 * @return the value of the current entry
		 */
		public V getValue();
	}
}
