/*
 * AbstractValueFactory.java - This file is part of the Jakstab project.
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

import java.util.Collection;

import org.jakstab.rtl.expressions.RTLNumber;

/**
 * AbstractValueFactory provides a mechanism for generic abstraction of
 * concrete values into an abstract domain. It is used by the ValuationState, 
 * VariableValuation, and PartitionedMemory classes.
 *   
 * @author Johannes Kinder
 * @param <A> The type of elements in the abstract domain 
 */
public interface AbstractValueFactory<A extends AbstractValue> {
	
	/**
	 * The abstraction function for a single concrete number.
	 * 
	 * @param n The concrete number to abstract, must be non-null.
	 * @return the abstract value corresponding to the provided number.
	 */
	public A createAbstractValue(RTLNumber n);
	
	/**
	 * The abstraction function for sets of concrete numbers.
	 * 
	 * @param n The set of concrete numbers to abstract, must be non-null.
	 * @return the single abstract value that abstracts all concrete 
	 * numbers in the set.
	 */
	public A createAbstractValue(Collection<RTLNumber> numbers);

	/**
	 * Creates the TOP element for this domain with a certain bit width.
	 * The object returned is not guaranteed to be unique. Bitvector type
	 * domains have several "TOP elements", one for each bit width. Joining
	 * TOP elements of several bit widths may cause an exception.
	 *  
	 * @param bitWidth the bit width of the top element.
	 * @return a TOP element of this domain with the specified bit width
	 */
	public A createTop(int bitWidth);

	/**
	 * Shorthand function for creating abstract elements of this domain
	 * abstracting the Boolean TRUE value.
	 * 
	 * @return An abstract value for TRUE.
	 */
	public A createTrue();

	/**
	 * Shorthand function for creating abstract elements of this domain
	 * abstracting the Boolean FALSE value.
	 * 
	 * @return An abstract value for FALSE.
	 */
	public A createFalse();

}
