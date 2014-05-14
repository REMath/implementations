/*
 * DummyAnalysis.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.dummy;

import java.util.Collections;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.CPAOperators;
import org.jakstab.analysis.ConfigurableProgramAnalysis;
import org.jakstab.analysis.Precision;
import org.jakstab.analysis.ReachedSet;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.util.Pair;

public class DummyAnalysis implements ConfigurableProgramAnalysis {
	
	public static void register(AnalysisProperties p) {
		p.setShortHand('d');
		p.setName("Dummy analysis");
		p.setDescription("Over-approximates all data to a single top element.");
	}
	
	final AbstractState top;
	
	public DummyAnalysis() {
		top = new DummyState();
	}
	
	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge, Precision precision) {
		return Collections.singleton(top);
	}

	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates, CFAEdge cfaEdge, Precision precision) {
		return null;
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
		return CPAOperators.mergeSep(s1, s2, precision);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopSep(s, reached, precision);
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	@Override
	public AbstractState initStartState(Location label) {
		return top;
	}

	@Override
	public Precision initPrecision(Location location,
			StateTransformer transformer) {
		return null;
	}

}
