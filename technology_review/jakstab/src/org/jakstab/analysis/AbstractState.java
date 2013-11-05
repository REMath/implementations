/*
 * AbstractState.java - This file is part of the Jakstab project.
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

import java.util.Set;

import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Tuple;

/**
 * @author Johannes Kinder
 */
public interface AbstractState extends LatticeElement {

	/**
	 * Get all possible combinations of concrete values for the given expressions in the 
	 * abstract state. A value of null in one of the returned tuples indicates the complete
	 * set of RTLNumbers of the matching type (bitwidth). The members of the tuples are
	 * in the same order as the given expressions.
	 *  
	 * @param expressions an array of expressions to evaluate and concretize 
	 * @return the set of possible combinations of concrete values for the given expressions.
	 */
	public Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression... expressions);

	@Override
	public AbstractState join(LatticeElement l);
	
	/**
	 * Get the abstracted program counter value in this state. Currently this is always an
	 * Location, but theoretically could be a code sequence, block, or the entire program.
	 * Only needs to be implemented by location analyses and composite states, other states
	 * can throw a runtime exception.
	 *  
	 * @return the location of this abstract state
	 */
	public Location getLocation();
	
	/**
	 * Return a string that identifies the current state, used only for debug messages.
	 * 
	 * @return an identifier for the current state, not required to be unique.
	 */
	public String getIdentifier();
	
}
