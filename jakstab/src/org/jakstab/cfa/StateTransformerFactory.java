/*
 * StateTransformerFactory.java - This file is part of the Jakstab project.
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

import org.jakstab.analysis.AbstractState;

/**
 * A factory for producing CFA edges from an abstract state and a program representation. 
 *
 * @author Johannes Kinder
 */
public interface StateTransformerFactory {
	
	/**
	 * Returns the set of CFA edges to be processed for calculating the abstract successor of
	 * a given abstract state. 
	 *  
	 * @param a the abstract state for calculating successors. The abstract state has to
	 * contain location information.
	 * @return the set of CFA edges from this abstract state
	 */
	public Set<CFAEdge> getTransformers(AbstractState a);
	
	/**
	 * Return the starting location for this view of the program. This can be
	 * either the program entry or exit, represented as a location.
	 *  
	 * @return the initial location
	 */
	public Location getInitialLocation();
	
}
