/*
 * SimpleCPA.java - This file is part of the Jakstab project.
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
 * Simplified interface for CPAs that do not use precision refinement.
 *  
 * @author Johannes Kinder
 */
public abstract class SimpleCPA implements ConfigurableProgramAnalysis {

	/**
	 * The abstract transfer function of the program analysis. For a given state,
	 * calculates the abstract successor states based on the supplied state 
	 * transformer. Returns null if the state does not have any successors.
	 * 
	 * @param state an abstract state
	 * @param cfaEdge the control flow edge
	 * @return the set of successor states
	 */
	public abstract Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge);

	/**
	 * Merge weakens the state s2 using information of state s1.
	 *  
	 * @param s1 the state used for weakening
	 * @param s2 the state to be weakened.
	 * @return a new state, which is greater or equal to s2 in the abstract domain.
	 */
	public abstract AbstractState merge(AbstractState s1, AbstractState s2);
	
	/**
	 * Stop checks whether the abstract state s is covered by the collection of
	 * states reached.
	 * 
	 * @param s the state to be checked
	 * @param reached a collection of states which will be checked for covering s
	 * @return true if s is covered by reached, false otherwise
	 */
	public abstract boolean stop(AbstractState s, ReachedSet reached);

	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge,
			Precision precision) {
		return post(state, cfaEdge);
	}
	
	@Override
	public AbstractState strengthen(AbstractState s,
			Iterable<AbstractState> otherStates, CFAEdge cfaEdge,
			Precision precision) {
		return null;
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2,
			Precision precision) {
		return merge(s1, s2);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return stop(s, reached);
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	@Override
	public Precision initPrecision(Location location,
			StateTransformer transformer) {
		return null;
	}

}
