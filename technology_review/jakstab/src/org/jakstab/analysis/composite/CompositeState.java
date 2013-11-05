/*
 * CompositeState.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.composite;

import java.util.Arrays;
import java.util.Set;

import org.jakstab.analysis.*;
import org.jakstab.analysis.location.LocationState;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;
import org.jakstab.util.Tuple;

/**
 * A cartesian product state that consists of a vector of substates where the 
 * first substate is guaranteed to be a location state.
 * 
 * @author Johannes Kinder
 */
public class CompositeState implements AbstractState {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CompositeState.class);
		
	protected final AbstractState[] components;
	
	/**
	 * @param components
	 */
	public CompositeState(AbstractState[] components) {
		super();
		this.components = components;
	}
	
	@Override
	public String getIdentifier() {
		StringBuilder id = new StringBuilder();
		id.append("ID");
		for (AbstractState c : components)
			id.append(c.getIdentifier()).append(":");
		return id.toString();
	}

	@Override
	public Location getLocation() {
		return ((LocationState)components[0]).getLocation();
	}
	
	public AbstractState getComponent(int index) {
		return components[index];
	}
	
	public int numComponents() {
		return components.length;
	}

	@Override
	public AbstractState join(LatticeElement l) {
		CompositeState other = (CompositeState)l;
		AbstractState[] jComponents = new AbstractState[components.length];
		for (int i=0; i<components.length; i++) {
			jComponents[i] = components[i].join(other.components[i]);
		}
		return new CompositeState(jComponents);
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {
		Set<Tuple<RTLNumber>> result = null;
		for (int i=0; i<components.length; i++) {
			// Concretize this component state and then intersect it with existing ones
			Set<Tuple<RTLNumber>> concreteTuples = components[i].projectionFromConcretization(expressions);
			//logger.info(concreteTuples);
			/* Return value of null represents the whole set of tuples of numbers (usually b/c the function 
			 * is not implemented), so intersection has no effect */ 
			if (concreteTuples == null) continue;
			/* If we are currently at the whole set, the new tuple set is the intersection */ 
			else if (result == null) result = concreteTuples;
			/* Else intersect */
			else {
				// result.retainAll(concreteTuples);
				// intersect manually b/c of possible null components (wildcards for more tuples)
				//   Note: A tuple with a null component expands to a set of tuples 
				//   with all possible values for that component
				//
				Set<Tuple<RTLNumber>> newResult = new FastSet<Tuple<RTLNumber>>();
				// for all tuples in result
				for (Tuple<RTLNumber> rTuple : result) {
					// for all tuples we got from the current substate 
					cTuplesLoop: for (Tuple<RTLNumber> cTuple : concreteTuples) {
						// array for building new tuple
						RTLNumber[] numbers = new RTLNumber[expressions.length];
						// match components of both tuples against each other
						for (int j=0; j<expressions.length; j++) {
							RTLNumber cNumber = cTuple.get(j);
							RTLNumber rNumber = rTuple.get(j);
							// if the component is no wildcard and not equal, don't match, try next new tuple for match
							if (cNumber != RTLNumber.WILDCARD && rNumber != null && !cNumber.equals(rNumber)) {
								continue cTuplesLoop;
							} else {
								// handle wildcards on both sides:
								if (rNumber == RTLNumber.WILDCARD) numbers[j] = cNumber;
								else numbers[j] = rNumber;
							}
						}
						// We passed all components - so add matching tuple
						newResult.add(Tuple.create(numbers));
						// We still need to continue with the next tuple, since wildcards
						// could allow more possibilities
					}
					// cTuplesLoop finished without finding a match
				}
				result = newResult;
			}
			
		}
		//logger.info("Project " + Arrays.toString(expressions) + " to " + result);
		assert result != null;
		return result;
	}

	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public boolean isTop() {
		return false;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		CompositeState other = (CompositeState)l;
		for (int i=0; i<components.length; i++) {
			if (!(components[i].lessOrEqual(other.components[i])))
				return false;
		}
		return true;
	}
	
	@Override
	public String toString() {
		StringBuilder res = new StringBuilder();
		res.append('(');
		for (int i=0; i<components.length - 1; i++) {
			res.append(components[i].toString());
			res.append(',');
		}
		res.append(components[components.length - 1].toString());
		res.append(')');
		return res.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + Arrays.hashCode(components);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		CompositeState other = (CompositeState) obj;
		if (!Arrays.equals(components, other.components))
			return false;
		return true;
	}
}
