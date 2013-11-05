/*
 * RTLVariableAssignment.java - This file is part of the Jakstab project.
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

import org.jakstab.rtl.*;
import org.jakstab.rtl.expressions.*;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * Assigns the value of the righthandside to the lefthandside variable.
 * 
 * @author Johannes Kinder
 */
public class RTLVariableAssignment extends AbstractRTLStatement implements RTLStatement {

	private static final Logger logger = Logger.getLogger(RTLVariableAssignment.class);

	private RTLVariable leftHandSide;
	private RTLExpression rightHandSide;

	public RTLVariableAssignment(int bitWidth, RTLVariable leftHandSide, RTLExpression rightHandSide) {
		super();
		this.leftHandSide = leftHandSide;
		this.rightHandSide = rightHandSide;
	}

	@Override
	public RTLStatement evaluate(Context context) {
		invalidateCache();
		RTLExpression evaldRHS = this.rightHandSide.evaluate(context);

		if (evaldRHS == null) logger.warn("No more RHS after evaluation of " + this.toString());
		
		ExpressionSimplifier simplifier = ExpressionSimplifier.getInstance();
		evaldRHS = simplifier.simplify(evaldRHS);

		// remove all killed assignments from the context
		context.removeAssignment(leftHandSide.getDefinedVariablesOnWrite());

		RTLExpression evaldLHS = this.leftHandSide.evaluate(context);

		if (evaldLHS.equals(evaldRHS)) {
			//logger.debug("Removed self-assignment: " + evaldLHS + " = " + evaldRHS);
			return null;
		}

		rightHandSide = evaldRHS;
		leftHandSide = (RTLVariable)evaldLHS;
		return this;
	}
	
	public RTLVariable getLeftHandSide() {
		return leftHandSide;
	}

	public RTLExpression getRightHandSide() {
		return rightHandSide;
	}

	@Override
	public void inferTypes(Architecture arch) throws TypeInferenceException {
		rightHandSide = rightHandSide.inferBitWidth(arch, leftHandSide.getBitWidth());
	}

	@Override
	public String toString() {
		StringBuilder res = new StringBuilder(255);

		res.append(leftHandSide);
		res.append(" := ");
		/*if (bitWidth > 0) res.append(bitWidth);
		else res.append('?');
		res.append("= ");*/
		res.append(rightHandSide);
		return res.toString();
	}

	@Override
	protected SetOfVariables initDefinedVariables() {
		return new SetOfVariables(leftHandSide.getDefinedVariablesOnWrite());
	}

	@Override
	protected SetOfVariables initUsedVariables() {
		SetOfVariables usedVariables = new SetOfVariables();
		usedVariables.addAll(leftHandSide.getUsedVariablesOnWrite());
		usedVariables.addAll(rightHandSide.getUsedVariables());
		return usedVariables;
	}

	@Override
	protected Set<RTLMemoryLocation> initUsedMemoryLocations() {
		Set<RTLMemoryLocation> usedMemory = new FastSet<RTLMemoryLocation>();
		usedMemory.addAll(leftHandSide.getUsedMemoryLocationsOnWrite());
		usedMemory.addAll(rightHandSide.getUsedMemoryLocations());
		return usedMemory;
	}

	@Override
	public <T> T accept(StatementVisitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result
				+ ((leftHandSide == null) ? 0 : leftHandSide.hashCode());
		result = prime * result
				+ ((rightHandSide == null) ? 0 : rightHandSide.hashCode());
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
		RTLVariableAssignment other = (RTLVariableAssignment) obj;
		if (leftHandSide == null) {
			if (other.leftHandSide != null)
				return false;
		} else if (!leftHandSide.equals(other.leftHandSide))
			return false;
		if (rightHandSide == null) {
			if (other.rightHandSide != null)
				return false;
		} else if (!rightHandSide.equals(other.rightHandSide))
			return false;
		return true;
	}
	
}
