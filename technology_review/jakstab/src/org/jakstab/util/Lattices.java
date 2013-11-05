/*
 * Lattices.java - This file is part of the Jakstab project.
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

import java.util.Collection;
import java.util.Iterator;

import org.jakstab.analysis.LatticeElement;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class Lattices {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(Lattices.class);

	@SuppressWarnings("unchecked")
	public static final <L extends LatticeElement> L joinAll(Collection<L> elementSet) {
		Iterator<L> iter = elementSet.iterator();
		L result = iter.next();
		while (iter.hasNext()) {
			result = (L)(result.join(iter.next()));
		}
		return result;
	}
	
	/**
	 * For a lattice element e and a collection C of lattice elements, returns an element r which
	 * is the join of e with a distinct member of C, and for which no join of e with a member of C is strictly
	 * less wrt. the lattice.
	 * Formally, returns r s.t. e \neq r \and (\exists x \in C. r = e \join x) \and (\not\exists x \in C. (e \join x) \lt r    
	 * @param <L> The lattice type
	 * @param e The lattice element to find a supremum for
	 * @param elementSet The set of lattice elements to choose from
	 * @return A lattice element greater or equal to e
	 */
	@SuppressWarnings("unchecked")
	public static final <L extends LatticeElement> L minimumJoin(L e, Collection<L> elementSet) {
		Iterator<L> iter = elementSet.iterator();
		L result = null;
		while (iter.hasNext()) {
			L newElement = (L)(e.join(iter.next()));
			if (!newElement.equals(e) && (result == null || newElement.lessOrEqual(result)))
				result = newElement;
		}
		assert (result != null); // Will fail if e is already larger than every other element in C
		return result;
	}
	
}
