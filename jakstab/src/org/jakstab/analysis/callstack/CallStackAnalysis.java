/*
 * CallStackAnalysis.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.callstack;

import java.util.Collections;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.*;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

/**
 * @author Johannes Kinder
 */
public class CallStackAnalysis implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setShortHand('s');
		p.setName("Call-stack analysis");
		p.setDescription("Maintain a history of call-sites for each location.");
	}

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CallStackAnalysis.class);
	
	
	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		return null;
	}

	@Override
	public AbstractState initStartState(Location label) {
		return new CallStackState();
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2,
			Precision precision) {
		return CPAOperators.mergeSep(s1, s2, precision);
	}

	@Override
	public Set<AbstractState> post(AbstractState state,
			CFAEdge cfaEdge, Precision precision) {
		return Collections.singleton(((CallStackState)state).abstractPost(cfaEdge.getTransformer(), precision));
	}

	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
			CFAEdge cfaEdge, Precision precision) {
		return s;
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopSep(s, reached, precision);
	}

}
