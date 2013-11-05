/*
 * DualCompositeState.java - This file is part of the Jakstab project.
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

import java.util.Collections;
import java.util.Set;

import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.UnderApproximateState;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;
import org.jakstab.util.Tuple;

/**
 * A composite state containing both over- and under-approximate states.
 * 
 * @author Johannes Kinder
 *
 */
public class DualCompositeState extends CompositeState {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(DualCompositeState.class);

	public DualCompositeState(AbstractState[] components) {
		super(components);
	}

	public Set<Tuple<RTLNumber>> projection(RTLExpression... expressions) {

		Set<Tuple<RTLNumber>> result = new FastSet<Tuple<RTLNumber>>();
		
		for (int i=0; i<components.length; i++) {
			if (!(components[i] instanceof UnderApproximateState)) 
				continue;
			// Concretize this component state and then take the union with existing ones
			Set<Tuple<RTLNumber>> concreteTuples = components[i].projectionFromConcretization(expressions);
			//logger.info(concreteTuples);
			/* Return value of null here represents the bottom element, so it has no effect in union */ 
			if (concreteTuples == null) continue;
			/* Else take the union */
			else {
				result.addAll(concreteTuples); 
			}
		}
		//logger.debug("Under-approximation projects " + Arrays.toString(expressions) + " to " + result);
		assert result != null;
		return result;
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {

		Set<Tuple<RTLNumber>> result = null;
		for (int i=0; i<components.length; i++) {
			if (components[i] instanceof UnderApproximateState) 
				continue;
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
		//assert result != null;
		
		// result can be null when using DummyAnalysis.
		if (result == null) result = Collections.emptySet();
		return result;
	}

}
