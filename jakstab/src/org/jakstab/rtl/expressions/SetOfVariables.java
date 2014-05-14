/*
 * SetOfVariables.java - This file is part of the Jakstab project.
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

package org.jakstab.rtl.expressions;

import java.io.Serializable;
import java.util.*;

import org.jakstab.util.Logger;

/**
 * A specialized set for variables, uses bitvectors to speed up set operations.
 * 
 * @author Johannes Kinder
 */
public class SetOfVariables extends AbstractSet<RTLVariable> implements Set<RTLVariable>, Serializable {
	
	public static final SetOfVariables EMPTY_SET = new SetOfVariables();

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(SetOfVariables.class);
	private static final long serialVersionUID = -5505393011046912608L;

	private final BitSet bitSet;

	public SetOfVariables() {
		bitSet = new BitSet(ExpressionFactory.DEFAULT_VARIABLE_COUNT);
	}
	
	public SetOfVariables(Collection<RTLVariable> collection) {
		this();
		addAll(collection);
	}

	public SetOfVariables(SetOfVariables proto) {
		this.bitSet = (BitSet)proto.bitSet.clone();
	}

	@Override
	public final boolean add(RTLVariable e) {
		if (bitSet.get(e.getIndex()))
			return false;
		bitSet.set(e.getIndex());
		return true;
	}

	@Override
	public final boolean addAll(Collection<? extends RTLVariable> c) {
		boolean changed = false;
		for(RTLVariable element : c) {
			changed |= add(element);
		}
		return changed;
	}
	
	/**
	 * Adds all elements of an array to this Set.
	 * 
	 * @param array the array to take the elements from
	 * @return true if this set was changed, false otherwise
	 */
	public final boolean addAll(RTLVariable[] array) {
		if (array == null) return false;
		boolean changed = false;
		for (int i=0; i<array.length; i++)
			changed |= this.add(array[i]);
		return changed;
	}

	public final void addAll(SetOfVariables vset) {
		bitSet.or(vset.bitSet);
	}

	@Override
	public final void clear() {
		bitSet.clear();
	}

	@Override
	public final boolean contains(Object o) {
		if (o instanceof RTLVariable) {
			return bitSet.get(((RTLVariable)o).getIndex());
		} else return false;
	}

	/*
	 * @see java.util.AbstractCollection#containsAll(java.util.Collection)
	 */
	@Override
	public final boolean containsAll(Collection<?> c) {
		if (c instanceof SetOfVariables) {
			SetOfVariables vset = (SetOfVariables)c;
			BitSet bitSetCopy = (BitSet)bitSet.clone();
			bitSetCopy.and(vset.bitSet);
			return bitSetCopy.equals(bitSet);
		} else {
			return super.containsAll(c);
		}
	}

	public boolean equals(SetOfVariables vset) {
		return vset != null && bitSet.equals(vset.bitSet);
	}

	@Override
	public int hashCode() {
		return bitSet.hashCode();
	}
	
	@Override
	public final boolean isEmpty() {
		return bitSet.isEmpty();
	}
	
	@Override
	public final Iterator<RTLVariable> iterator() {
		return new Iterator<RTLVariable>() {
			private int index = 0;
			@Override
			public boolean hasNext() {
				return (bitSet.nextSetBit(index) >= 0);
			}
			@Override
			public RTLVariable next() {
				int nextSet = bitSet.nextSetBit(index);
				index = nextSet + 1;
				return ExpressionFactory.getVariable(nextSet);
			}
			@Override
			public void remove() {
				bitSet.clear(index - 1);
			}
		};
	}

	@Override
	public final boolean remove(Object o) {
		if (o instanceof RTLVariable) {
			RTLVariable var = (RTLVariable)o;
			if (!bitSet.get(var.getIndex()))
				return false;
			else {
				bitSet.clear(var.getIndex());
				return true;
			}
		} else return false;
	}
	
	@Override
	public final boolean removeAll(Collection<?> c) {
		if (c instanceof SetOfVariables) {
			SetOfVariables vset = (SetOfVariables)c;
			if (bitSet.intersects(vset.bitSet)) {
				bitSet.andNot(vset.bitSet);
				return true;
			} else return false;
		} else {
			return super.removeAll(c);
		}
	}

	public final void removeAll(SetOfVariables vset) {
		bitSet.andNot(vset.bitSet);
	}
	
	/*
	 * @see java.util.AbstractCollection#retainAll(java.util.Collection)
	 */
	@Override
	public final boolean retainAll(Collection<?> c) {
		if (c instanceof SetOfVariables) {
			SetOfVariables vset = (SetOfVariables)c;
			if (!bitSet.equals(vset.bitSet)) {
				bitSet.and(vset.bitSet);
				return true;
			} else return false;
		} else {
			return super.retainAll(c);
		}
	}
	
	public final void retainAll(SetOfVariables vset) {
		bitSet.and(vset.bitSet);
	}

	@Override
	public final int size() {
		return bitSet.cardinality();
	}
	
}
