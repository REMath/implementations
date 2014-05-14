/*
 * ReverseCFATransformerFactory.java - This file is part of the Jakstab project.
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
package org.jakstab.cfa;

import java.util.HashSet;
import java.util.Set;

import org.jakstab.analysis.AbstractState;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.statements.RTLSkip;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

public class ReverseCFATransformerFactory implements StateTransformerFactory {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ReverseCFATransformerFactory.class);
	
	private SetMultimap<Location,CFAEdge> reverseCFA;
	private Location sink;
	
	public ReverseCFATransformerFactory(Set<CFAEdge> cfa) {
		reverseCFA = HashMultimap.create();
		Set<Location> nonSinks = new HashSet<Location>();
		for (CFAEdge e : cfa) {
			reverseCFA.put(e.getTarget(), e);
			nonSinks.add(e.getSource());
		}
		
		FastSet<Location> sinks = new FastSet<Location>();
		for (Location l : reverseCFA.keySet()) {
			if (!nonSinks.contains(l)) {
				sinks.add(l);
			}
		}
		
		if (sinks.size() == 1) {
			sink = sinks.pick();
		} else if (sinks.size() == 0) {
			throw new RuntimeException("CFA has no sink!");
		} else {
			// Generate artificial exit node
			sink = new Location(new AbsoluteAddress(0xFFFFFF01L));
			for (Location l : sinks) {
				reverseCFA.put(sink, new CFAEdge(l, sink, new RTLSkip()));
			}
		}
	}

	@Override
	public Set<CFAEdge> getTransformers(AbstractState a) {
		return reverseCFA.get(a.getLocation());
	}

	@Override
	public Location getInitialLocation() {
		return sink;
	}
}
