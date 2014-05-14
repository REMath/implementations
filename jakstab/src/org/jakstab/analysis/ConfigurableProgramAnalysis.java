/*
 * ConfigurableProgramAnalysis.java - This file is part of the Jakstab project.
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

import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.util.Pair;

/**
 * A configurable program analysis (CPA), following the abstract interpretation
 * framework of Dirk Beyer and Tom Henzinger.
 * 
 * @author Johannes Kinder
 */
public interface ConfigurableProgramAnalysis {
	
	/**
	 * The abstract transfer function of the program analysis. For a given state,
	 * calculates the abstract successor states based on the supplied state 
	 * transformer. Returns null if the state does not have any successors.
	 * 
	 * @param state an abstract state
	 * @param cfaEdge the control flow edge
	 * @param precision the current precision
	 * @return the set of successor states
	 */
	public Set<AbstractState> post(final AbstractState state, CFAEdge cfaEdge, Precision precision);

	/**
	 * Strengthens state s using information from other states. This method will 
	 * be called by a composite analysis after computing post to improve precision 
	 * beyond a purely cartesian combination of analyses. 
	 *  
	 * @param s an abstract state
	 * @param otherStates a sequence of states from different analyses
	 * @param cfaEdge the control flow edge that produced s and the other states
	 * @param precision the current precision
	 * @return a strengthened copy of s or the unmodified s
	 */
	public AbstractState strengthen(AbstractState s, final Iterable<AbstractState> otherStates, CFAEdge cfaEdge, Precision precision);
			
	/**
	 * Merge weakens the state s2 using information of state s1.
	 *  
	 * @param s1 the state used for weakening
	 * @param s2 the state to be weakened.
	 * @param precision the current precision 
	 * @return a new state, which is greater or equal to s2 in the abstract domain.
	 */
	public AbstractState merge(final AbstractState s1, final AbstractState s2, Precision precision);

	/**
	 * Stop checks whether the abstract state s is covered by the collection of
	 * states reached.
	 * 
	 * @param s the state to be checked
	 * @param reached a collection of states which will be checked for covering s
	 * @param precision the current precision
	 * @return true if s is covered by reached, false otherwise
	 */
	public boolean stop(final AbstractState s, ReachedSet reached, Precision precision);
	
	/**
	 * Adjusts the precision of a state using information taken from the set of all
	 * reached states. 
	 * 
	 * @param s the state to adjust
	 * @param precision the precision of state s
	 * @param reached the set of reached states
	 * @return the possibly widened state s and a new, adjusted precision object
	 */
	public Pair<AbstractState, Precision> prec(final AbstractState s, Precision precision, ReachedSet reached);
	
	/**
	 * Initializes an abstract state with initial valuations using a given program 
	 * counter value
	 * 
	 * @param label the initial location for this analysis
	 * @return the new abstract initial state
	 */
	public AbstractState initStartState(Location label);

	/**
	 * Initializes a precision object every time a new location is reached.

	 * @param location the location for which this precision is created
	 * @param transformer the transformer by which this new location was reached.
	 * @return the initial precision
	 */
	public Precision initPrecision(Location location, StateTransformer transformer);
}
