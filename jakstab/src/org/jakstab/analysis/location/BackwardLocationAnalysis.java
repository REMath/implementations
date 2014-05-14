/*
 * LocationAnalysis.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.location;


import java.util.Collections;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.*;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.util.Logger;

/**
 * An inverse one-state-per-statement location analysis.
 * 
 * @author Johannes Kinder
 */
public class BackwardLocationAnalysis extends LocationAnalysis implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setName("Backward location analysis");
		p.setDescription("A backward location analysis, used for backward analyses.");
	}

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(BackwardLocationAnalysis.class);

	public BackwardLocationAnalysis() {
		super();
	}

	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cFAEdge, Precision precision) {
		LocationState cs = (LocationState)state;
		if (cs.isBot()) return Collections.singleton((AbstractState)LocationState.BOT);
		return Collections.singleton((AbstractState)new LocationState(cFAEdge.getSource()));
	}

}
