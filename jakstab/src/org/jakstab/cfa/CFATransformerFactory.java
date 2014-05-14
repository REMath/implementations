/*
 * CFATransformerFactory.java - This file is part of the Jakstab project.
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

import java.util.Set;

import org.jakstab.Program;
import org.jakstab.analysis.AbstractState;
import org.jakstab.util.Logger;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;

/**
 * Trivial implementation that provides CFA edges from an already reconstructed
 * control flow automaton. 
 * 
 * @author Johannes Kinder
 */
public class CFATransformerFactory implements StateTransformerFactory {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CFATransformerFactory.class);
	
	private SetMultimap<Location,CFAEdge> cfa;
	
	public CFATransformerFactory(Set<CFAEdge> cfa) {
		this.cfa = HashMultimap.create();
		for (CFAEdge e : cfa) {
			this.cfa.put(e.getSource(), e);
		}
	}

	/*
	 * @see org.jakstab.analysis.StateTransformerFactory#getTransformers(org.jakstab.analysis.AbstractState)
	 */
	@Override
	public Set<CFAEdge> getTransformers(AbstractState a) {
		Set<CFAEdge> cfaEdges = cfa.get(a.getLocation());
		return cfaEdges;
	}

	@Override
	public Location getInitialLocation() {
		return Program.getProgram().getStart();
	}
}
