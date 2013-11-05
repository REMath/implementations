/*
 * FastSet.java - This file is part of the Jakstab project.
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
import java.io.Serializable;

/**
 * A fast Set implementation that maintains its members as an ArrayList as
 * long as it is small in size, and changes to a LinkedHashSet once it
 * grows large enough to amortize the cost of hashing functions.
 *
 * @author Johannes Kinder
 */
public class FastSet<E> extends AbstractSet<E> implements Set<E>, Serializable, Worklist<E>
{
	private static final long serialVersionUID = -7387536630587627888L;
	private static final int SMALL_CAPACITY = 15;
	private static final int LARGE_CAPACITY = 100;
	private static int conversions = 0;
	
	public static int getConversionCount() { return conversions; }
	
	private int capacity;
	private Collection<E> collection;
	
	public FastSet(int initialCapacity) {
		this.capacity = initialCapacity;
		if (initialCapacity <= SMALL_CAPACITY)
			collection = new ArrayList<E>(initialCapacity);
		else 
			collection = new LinkedHashSet<E>(initialCapacity);
	}

	/**
	 * Creates a new FastSet with a small default capacity.
	 */
	public FastSet() {
		this(SMALL_CAPACITY);
	}

	/**
	 * Create a new FastSet with the same elements as the
	 * given collection.
	 *
	 * @param elements the elements for the new FastSet
	 */
	public FastSet(final Collection<? extends E> elements) {
		this(elements.size());
		this.addAll(elements);
	}
	
	/**
	 * Creates a new FastSet with only the given element
	 * as the single member.
	 * 
	 * @param element the element for the new FastSet
	 */
	public FastSet(E element) {
		this(1);
		this.add(element);
	}

	/**
	 * Returns the size of the set.
	 *
	 * @return The current size of the set.
	 */
	@Override
	public final int size() {
		return collection.size();
	}

	@Override
	public final Iterator<E> iterator() {
		return collection.iterator();
	}

	/**
	 * Adds an element to the set.
	 *
	 * @param e Element to add.
	 * @return True if the set was changed, false otherwise.
	 */
	@Override
	public final boolean add(final E e) {
		// Explicit contains check necessary since ArrayList does not enforce set property 
		if (collection.contains(e)) return false;
		
		/* The first time we hit the small capacity threshold, convert the
		 * collection to a hashset.*/
		if (collection.size() - 1 == SMALL_CAPACITY && capacity <= SMALL_CAPACITY) {
			LinkedHashSet<E> newCollection = new LinkedHashSet<E>(LARGE_CAPACITY);
			newCollection.addAll(collection);
			collection = newCollection;
			capacity = LARGE_CAPACITY;
			conversions++;
		}

		// Returns whether the set already contains e
		return collection.add(e);
	}
	
	/**
	 * Adds all elements of an array to this Set.
	 * 
	 * @param array the array to take the elements from
	 * @return true if this set was changed, false otherwise
	 */
	public final boolean addAll(E[] array) {
		if (array == null) return false;
		boolean changed = false;
		for (int i=0; i<array.length; i++)
			changed |= this.add(array[i]);
		return changed;
	}

	/**
	 * Return whether this set is empty.
	 *
	 * @return True if the set has a size of 0.
	 */
	@Override
	public final boolean isEmpty() {
		return collection.isEmpty();
	}

	/**
	 * Returns true if this set contains the specified element.
	 *
	 * @param obj Element to be looked for.
	 * @return true if the set contains the given element.
	 */
	@Override
	public final boolean contains(final Object obj) {
		return collection.contains(obj);
	}

	/**
	 * Removes the given element from this set if present.
	 *
	 * @param obj Element to be removed.
	 * @return True if the element was removed, false if it was not present.
	 */
	@Override
	public final boolean remove(final Object obj) {
		return collection.remove(obj);
	}

	/**
	 * Removes all elements from this set.
	 */
	public final void clear() {
		collection.clear();
	}

	/**
	 * Returns a new set which is the intersection of
	 * this set and the other set given. Both original
	 * sets are unchanged by this operation.
	 *  
	 * @param other the other set to intersect with this set.
	 * @return the intersection as a new set.
	 */
	public final FastSet<E> intersection(Set<? extends E> other) {
		FastSet<E> tmp = new FastSet<E>(this);
		tmp.retainAll(other);
		return tmp;
	}
	
	/**
	 * Returns a new set which is the union of
	 * this set and the other set given. Both original
	 * sets are unchanged by this operation.
	 *  
	 * @param other the other set to unite with this set.
	 * @return the union as a new set.
	 */
	public final FastSet<E> union(Set<? extends E> other) {
		FastSet<E> tmp = new FastSet<E>(this);
		tmp.addAll(other);
		return tmp;
	}
	
	/**
	 * Picks and removes an element from the set (actually
	 * the first one returned by iterator).
	 * 
	 * @return an element from the set.
	 */
	@Override
	public final E pick() {
		Iterator<E> i = iterator();
		E element = i.next();
		i.remove();
		return element;
	}
}