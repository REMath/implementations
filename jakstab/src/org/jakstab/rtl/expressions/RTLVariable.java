/*
 * RTLVariable.java - This file is part of the Jakstab project.
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
import org.jakstab.rtl.TypeInferenceException;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;

/**
 * Variables, which can be registers, temporary variables, or template variables in SSL instructions.
 * ExpressionFactory ensures that only one copy of each variable exists at runtime.
 * 
 * @author Johannes Kinder
 */
public class RTLVariable extends AbstractRTLExpression implements RTLExpression, Writable, Comparable<RTLVariable> {
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLVariable.class);

	public static final int UNKNOWN_BITWIDTH = Integer.MIN_VALUE;
	
	private final String name;
	private SetOfVariables setOfThis;
	private final int bitWidth;
	private final int index;
	
	protected RTLVariable(int index, String name, int bitWidth) {
		this.name = name;
		this.bitWidth = bitWidth;
		this.index = index;
		this.setOfThis = new SetOfVariables();
		this.setOfThis.add(this);
	}
	
	protected RTLVariable(int index, String name) {
		this(index, name, UNKNOWN_BITWIDTH);
	}

	@Override
	public RTLExpression evaluate(Context context) {
		RTLExpression subst = context.getSubstitution(this);
		if (subst instanceof Writable) {
			RTLExpression value = context.getAssignment((Writable)subst);
			if (value != null) return value;
		} 
		return subst; 
	}

	/**
	 * @return the name of this variable
	 */
	public String getName() {
		return name;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return name;
	}

	@Override
	public SetOfVariables getUsedVariables() {
		if (usedVariables == null) {
			usedVariables = new SetOfVariables();
			usedVariables.add(this);
		}
		return usedVariables;
	}
	
	@Override
	public SetOfVariables getUsedVariablesOnWrite() {
		return SetOfVariables.EMPTY_SET;
	}

	@Override
	public SetOfVariables getDefinedVariablesOnWrite() {
		return setOfThis;
	}

	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocations() {
		return Collections.emptySet();
	}

	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocationsOnWrite() {
		return Collections.emptySet();
	}

	@Override
	public Set<RTLMemoryLocation> getDefinedMemoryLocationsOnWrite() {
		return Collections.emptySet();
	}

	@Override
	public int compareTo(RTLVariable o) {
		if (o.index > index) return 1;
		if (o.index < index) return -1;
		return 0;
	}

	public int getBitWidth() {
		return bitWidth;
	}

	public int getIndex() {
		return index;
	}

	@Override
	public int size() {
		return 1;
	}
	
	/*
	 * @see org.jakstab.rtl.expressions.AbstractRTLExpression#inferBitWidth(org.jakstab.ssl.Architecture, int)
	 */
	@Override
	public RTLExpression inferBitWidth(Architecture arch, int expectedBitWidth)
			throws TypeInferenceException {
		if (bitWidth != expectedBitWidth) {
			throw new TypeInferenceException("Expected " + this + " to be " + expectedBitWidth + " bits, but is " + getBitWidth());
		}
		return this;
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
