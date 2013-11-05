/*
 * AbstractRTLStatement.java - This file is part of the Jakstab project.
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

package org.jakstab.rtl.statements;

import java.util.Set;

import org.jakstab.cfa.Location;
import org.jakstab.rtl.TypeInferenceException;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.SetOfVariables;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;
import org.jakstab.asm.AbsoluteAddress;

/**
 * Abstract class for operations common to many statements.
 * 
 * @author Johannes Kinder
 */
public abstract class AbstractRTLStatement implements RTLStatement, Cloneable {
	
	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(AbstractRTLStatement.class);

	/**
	 * Cached results for simple queries.
	 */
	protected SetOfVariables usedVariables = null;
	protected SetOfVariables definedVariables = null;
	protected Set<RTLMemoryLocation> usedMemoryLocations = null;

	protected Location label;
	protected Location nextLabel;

	protected void invalidateCache() {
		usedVariables = null;
		definedVariables = null;
		usedMemoryLocations = null;
	}
	
	/*
	 * @see org.jakstab.rtl.RTLStatement#getDefinedVariables()
	 */
	@Override
	public SetOfVariables getDefinedVariables() {
		if (definedVariables == null) {
			definedVariables = initDefinedVariables();
		}
		return definedVariables;
	}

	protected abstract SetOfVariables initDefinedVariables();

	/*
	 * @see org.jakstab.rtl.RTLStatement#getUsedVariables()
	 */
	@Override
	public SetOfVariables getUsedVariables() {
		if (usedVariables == null) {
			usedVariables = initUsedVariables();
		}
		return usedVariables;
	}

	protected abstract SetOfVariables initUsedVariables();

	
	/*
	 * @see org.jakstab.rtl.RTLStatement#getUsedMemoryLocations()
	 */
	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocations() {
		if (usedMemoryLocations == null) {
			usedMemoryLocations = initUsedMemoryLocations();
		}
		return usedMemoryLocations;
	}

	protected abstract Set<RTLMemoryLocation> initUsedMemoryLocations();
	
	/*
	 * @see org.jakstab.rtl.RTLStatement#getLabel()
	 */
	public Location getLabel() {
		return label;
	}

	/*
	 * @see org.jakstab.rtl.RTLStatement#setLabel(org.jakstab.asm.AbsoluteAddress, int)
	 */
	public void setLabel(AbsoluteAddress addr, int rtlId) {
		this.label = new Location(addr, rtlId);
	}
	
	@Override
	public void setLabel(Location label) {
		this.label = label;
	}

	/*
	 * @see org.jakstab.rtl.RTLStatement#getAddress()
	 */
	public AbsoluteAddress getAddress() {
		return label.getAddress();
	}

	/*
	 * @see org.jakstab.rtl.RTLStatement#isInstantiated()
	 */
	public boolean isInstantiated() {
		return label != null;
	}

	/*
	 * @see org.jakstab.rtl.RTLStatement#inferTypes()
	 */
	public void inferTypes(Architecture arch) throws TypeInferenceException {
		return;
	}
	
	/*
	 * @see org.jakstab.rtl.RTLStatement#shallowCopy()
	 */
	public RTLStatement copy() {
		return (RTLStatement)clone();
	}

	/**
	 * Performs a shallow clone of this statement.
	 * 
	 * @return a shallow clone of this statement.
	 * @see java.lang.Object#clone()
	 */
	@Override
	protected Object clone() {
		AbstractRTLStatement result;
		try {
			result = (AbstractRTLStatement)super.clone();
		} catch (CloneNotSupportedException e) {
			throw new InternalError(e.getMessage());
		}
		result.invalidateCache();
		return result;
	}
	
	/*
	 * @see java.lang.Comparable#compareTo(java.lang.Object)
	 */
	@Override
	public int compareTo(RTLStatement o) {
		if (this.equals(o)) return 0;
		int res = label.compareTo(o.getLabel());
		if (res != 0) return res;
		throw new IllegalStateException("Comparing two non-equal RTLStatements with the same label: "
				+ this.label + " " + o.getLabel());
	}

	@Override
	public Location getNextLabel() {
		return nextLabel;
	}

	@Override
	public void setNextLabel(Location nextLabel) {
		this.nextLabel = nextLabel;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((label == null) ? 0 : label.hashCode());
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
		AbstractRTLStatement other = (AbstractRTLStatement) obj;
		if (label == null) {
			if (other.label != null)
				return false;
		} else if (!label.equals(other.label))
			return false;
		return true;
	}
}
