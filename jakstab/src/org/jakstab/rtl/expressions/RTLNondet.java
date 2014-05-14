/*
 * RTLNondet.java - This file is part of the Jakstab project.
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

package org.jakstab.rtl.expressions;

import java.util.Collections;
import java.util.Set;

import org.jakstab.rtl.Context;
import org.jakstab.util.Logger;

/**
 * A nondeterministic integer value of a specified bit width. Two nondet expressions
 * are never equal to avoid nondet=nondet simplifications during evaluation.
 * 
 * @author Johannes Kinder
 */
public class RTLNondet extends AbstractRTLExpression implements RTLExpression {

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(RTLNondet.class);
	private final int bitWidth;
	private final String name;
	
	/**
	 * @param bitWidth
	 */
	public RTLNondet(int bitWidth) {
		super();
		this.bitWidth = bitWidth;
		this.name = "nondet" + bitWidth; 
	}

	/*
	 * @see org.jakstab.rtl.RTLExpression#evaluate(org.jakstab.rtl.Context)
	 */
	@Override
	public RTLExpression evaluate(Context context) {
		return this;
	}

	/*
	 * @see org.jakstab.rtl.RTLExpression#getUsedVariables()
	 */
	@Override
	public SetOfVariables getUsedVariables() {
		return SetOfVariables.EMPTY_SET;
	}

	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocations() {
		return Collections.emptySet();
	}

	/*
	 * @see org.jakstab.rtl.RTLExpression#size()
	 */
	@Override
	public int size() {
		return 1;
	}
	
	/*
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		// Required for correct evaluation, otherwise "nondet == nondet" might evaluate to true...
		return false;
	}

	/**
	 * @return the bitWidth
	 */
	public int getBitWidth() {
		return bitWidth;
	}

	/*
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return name;
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
