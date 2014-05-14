/*
 * Tuple.java - This file is part of the Jakstab project.
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

import java.util.Arrays;
import java.util.Iterator;

import org.jakstab.util.Logger;

/**
 * Array wrapper for better support of generics. Does not perform type safety checks!
 * 
 * @author Johannes Kinder
 */
public class Tuple<T> implements Iterable<T> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(Tuple.class);
	
	public static <T> Tuple<T> create(T... elements) {
		Tuple<T> tuple = new Tuple<T>(elements.length);
		tuple.array = elements;
		return tuple;
	}
	
	private Object[] array;
	
	public Tuple(int arity) {
		array = new Object[arity];
	}
	
	@SuppressWarnings("unchecked")
	public T get(int index) {
		return (T)array[index];
	}
	
	public void set(int index, T value) {
		array[index] = value;
	}
	
	public int size() {
		return array.length;
	}
	
	@Override
	public int hashCode() {
		return 31 + Arrays.hashCode(array);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Tuple<?> other = (Tuple<?>) obj;
		if (!Arrays.equals(array, other.array))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return Arrays.toString(array);
	}

	@Override
	public Iterator<T> iterator() {
		return new Iterator<T>() {
			int i=0;

			@Override
			public boolean hasNext() {
				return i < size();
			}

			@Override
			public T next() {
				return get(i++);
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}
		};
	}

}
