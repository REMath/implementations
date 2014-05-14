/*
 * ProcedureState.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.procedures;

import java.util.Set;

import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;
import org.jakstab.util.Tuple;

/**
 * @author Johannes Kinder
 */
public class ProcedureState implements AbstractState {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(ProcedureState.class);
	
	private FastSet<Location> procedureEntries;

	public ProcedureState(FastSet<Location> procedureEntries) {
		this.procedureEntries = procedureEntries;
	}
	
	public Set<Location> getProcedureEntries() {
		return procedureEntries;
	}

	/*
	 * @see org.jakstab.analysis.AbstractState#getIdentifier()
	 */
	@Override
	public String getIdentifier() {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * @see org.jakstab.analysis.AbstractState#getLocation()
	 */
	@Override
	public Location getLocation() {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * @see org.jakstab.analysis.AbstractState#join(org.jakstab.analysis.LatticeElement)
	 */
	@Override
	public AbstractState join(LatticeElement l) {
		ProcedureState other = (ProcedureState)l;
		return new ProcedureState(other.procedureEntries.union(this.procedureEntries));
	}

	/*
	 * @see org.jakstab.analysis.AbstractState#projectionFromConcretization(org.jakstab.rtl.expressions.RTLExpression[])
	 */
	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * @see org.jakstab.analysis.LatticeElement#isBot()
	 */
	@Override
	public boolean isBot() {
		return procedureEntries.isEmpty();
	}

	/*
	 * @see org.jakstab.analysis.LatticeElement#isTop()
	 */
	@Override
	public boolean isTop() {
		return procedureEntries == null;
	}

	/*
	 * @see org.jakstab.analysis.LatticeElement#lessOrEqual(org.jakstab.analysis.LatticeElement)
	 */
	@Override
	public boolean lessOrEqual(LatticeElement l) {
		ProcedureState other = (ProcedureState)l;
		return other.isTop() || other.procedureEntries.containsAll(this.procedureEntries);
	}

	@Override
	public String toString() {
		return procedureEntries.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime
				* result
				+ ((procedureEntries == null) ? 0 : procedureEntries.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		ProcedureState other = (ProcedureState) obj;
		if (procedureEntries == null) {
			if (other.procedureEntries != null)
				return false;
		} else if (!procedureEntries.equals(other.procedureEntries))
			return false;
		return true;
	}
	
}
