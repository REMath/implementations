/*
 * LatticeElement.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis;

/**
 * An interface representing an element of a semi-lattice.
 * 
 * @author Johannes Kinder
 */
public interface LatticeElement {
	
	/**
	 * Returns the join (supremum) of this lattice element and another element
	 * of the same lattice. 
	 * This method has to observe the contract
	 *        x.join(y) = y.join(x)
	 *    and x.lessOrEqual(x.join(y)) && y.lessOrEqual(x.join(y))
	 * 
	 * @param l the lattice element to join with.
	 * @return the join of both elements.
	 */
	public LatticeElement join(LatticeElement l);

	/**
	 * Returns whether this lattice elements is less or equal to another one. 
	 * This method observes the contract:
	 *         x.lessOrEqual(y) && y.lessOrEqual(x) <=> x.equals(y)
     *
	 * @param l the lattice element to compare to.
	 * @return true, if this element is less or equal to l.
	 */
	public boolean lessOrEqual(LatticeElement l);
	
	/**
	 * Check to see whether this element is the top element. May be implemented
	 * through a reference check to a unique top element.
	 *   
	 * @return True if this is the top element.
	 */
	public boolean isTop();
	
	/**
	 * Check to see whether this element is the bottom element. May be implemented
	 * through a reference check to a unique bottom element.
	 *   
	 * @return True if this is the bottom element.
	 */
	public boolean isBot();
	
	/**
	 * Returns whether this lattice elements is equivalent to another one. 
	 * This method observes the contract:
	 *         x.lessOrEqual(y) && y.lessOrEqual(x) <=> x.equals(y)
	 *     and x.equals(y) <=> y.equals(x)
	 *     
	 * @param o the object to compare to.
	 * @return true, if o is a lattice element equivalent to this element
	 */
	@Override
	public boolean equals(Object o);

}
