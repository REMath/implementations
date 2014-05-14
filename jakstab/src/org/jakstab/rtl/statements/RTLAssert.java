/*
 * RTLAssert.java - This file is part of the Jakstab project.
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

import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.SetOfVariables;
import org.jakstab.util.Logger;

/**
 * An assertion which can be verified by an analysis but has no other effect on program behavior.
 * 
 * @author Johannes Kinder
 */
public class RTLAssert extends AbstractRTLStatement implements RTLStatement {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLAssert.class);
	
	private RTLExpression assertion;

	/**
	 * @param assertion
	 */
	public RTLAssert(RTLExpression assertion) {
		super();
		this.assertion = assertion;
	}
	
	/*
	 * @see org.jakstab.rtl.AbstractRTLStatement#initDefinedVariables()
	 */
	@Override
	protected SetOfVariables initDefinedVariables() {
		return SetOfVariables.EMPTY_SET;
	}

	/*
	 * @see org.jakstab.rtl.AbstractRTLStatement#initUsedMemoryLocations()
	 */
	@Override
	protected Set<RTLMemoryLocation> initUsedMemoryLocations() {
		return assertion.getUsedMemoryLocations();
	}

	/*
	 * @see org.jakstab.rtl.AbstractRTLStatement#initUsedVariables()
	 */
	@Override
	protected SetOfVariables initUsedVariables() {
		return assertion.getUsedVariables();
	}
	
	public RTLExpression getAssertion() {
		return assertion;
	}

	/*
	 * @see org.jakstab.rtl.RTLStatement#accept(org.jakstab.rtl.StatementVisitor)
	 */
	@Override
	public <T> T accept(StatementVisitor<T> visitor) {
		return visitor.visit(this);
	}

	/*
	 * @see org.jakstab.rtl.RTLStatement#evaluate(org.jakstab.rtl.Context)
	 */
	@Override
	public RTLStatement evaluate(Context context) {
		invalidateCache();
		assertion = assertion.evaluate(context);
		return this;
	}

	/*
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "assert " + assertion.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result
				+ ((assertion == null) ? 0 : assertion.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		RTLAssert other = (RTLAssert) obj;
		if (assertion == null) {
			if (other.assertion != null)
				return false;
		} else if (!assertion.equals(other.assertion))
			return false;
		return true;
	}
	
}
