/*
 * AssignmentTemplate.java - This file is part of the Jakstab project.
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
import org.jakstab.rtl.TypeInferenceException;
import org.jakstab.rtl.expressions.*;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * A template for variable and memory assignments, before the left hand side has been
 * typed by instantiating the "modrm" placeholders. 
 * 
 * @author Johannes Kinder
 */
public class AssignmentTemplate extends AbstractRTLStatement {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger
			.getLogger(AssignmentTemplate.class);

	private int bitWidth;
	private Writable leftHandSide;
	private RTLExpression rightHandSide;

	public AssignmentTemplate(int bitWidth, Writable leftHandSide, RTLExpression rightHandSide) {
		super();
		this.bitWidth = bitWidth;
		this.leftHandSide = leftHandSide;
		this.rightHandSide = rightHandSide;
	}

	@Override
	public RTLStatement evaluate(Context context) {
		invalidateCache();
		RTLExpression evaldRHS = this.rightHandSide.evaluate(context);
		int evaldBitWidth = this.bitWidth;

		if (evaldRHS == null) logger.warn("No more RHS after evaluation of " + this.toString());

		// remove all killed assignments from the context
		context.removeAssignment(leftHandSide.getDefinedVariablesOnWrite());

		RTLExpression evaldLHS = this.leftHandSide.evaluate(context);

		if (evaldLHS.equals(evaldRHS)) {
			//logger.debug("Removed self-assignment: " + evaldLHS + " = " + evaldRHS);
			return null;
		}

		/*
		// Only do this if the statement has already been instantiated
		if (isInstantiated()) {
			// Remove bitranges on LHS
			if (evaldLHS instanceof RTLBitRange) {
				//logger.debug("Normalizing bitrange: " + evaldLHS + " :=" +evaldBitWidth + "= " + evaldRHS);
				RTLBitRange bitrange = (RTLBitRange)evaldLHS;
				
				evaldRHS = bitrange.applyInverse(evaldRHS);
				evaldLHS = bitrange.getOperand();
				
				// Recurse
				evaldRHS = evaldRHS.evaluate(context);
				evaldLHS = evaldLHS.evaluate(context);
				// Set bitwidth of the assignment to variable width
				evaldBitWidth = ((Writable)evaldLHS).getBitWidth();
				//logger.debug("Result: " + evaldLHS + " :=" + evaldBitWidth + "= " + evaldRHS);
			}

			RTLStatement newStmt;
			
			// Now make this a proper assignment to either variable or memory				
			if (evaldLHS instanceof RTLVariable) {
				assert evaldBitWidth == evaldLHS.getBitWidth();
				newStmt = new RTLVariableAssignment(evaldBitWidth, (RTLVariable)evaldLHS, evaldRHS);
			} else if (evaldLHS instanceof RTLMemoryLocation) {
				assert evaldBitWidth == evaldLHS.getBitWidth();
				newStmt = new RTLMemoryAssignment((RTLMemoryLocation)evaldLHS, evaldRHS);
			} else {
				throw new RuntimeException("Lefthandside of assignment is neither variable nor memory after instantiation.");
			}
			
			// Make sure the statement is labeled
			newStmt.setLabel(getLabel());
			newStmt.setNextLabel(getNextLabel());
			return newStmt;
			
		} else { 
			*/

			bitWidth = evaldBitWidth;
			rightHandSide = evaldRHS;
			if (evaldLHS instanceof Writable) {
				leftHandSide = (Writable)evaldLHS;
			} else {
				logger.error("Error: LHS of assignment no longer writable after evaluation: " + 
						this.leftHandSide.toString() + " = " + evaldLHS.toString());
			}
			return this;
	//	}
	}
	
	public RTLStatement convertToSpecificAssignmentType() {
		
		RTLExpression evaldLHS = leftHandSide;
		RTLExpression evaldRHS = rightHandSide;
		
		/* Remove bitranges on LHS */
		if (evaldLHS instanceof RTLBitRange) {
			//logger.debug("Normalizing bitrange: " + evaldLHS + " :=" +evaldBitWidth + "= " + evaldRHS);
			RTLBitRange bitrange = (RTLBitRange)evaldLHS;
			
			evaldRHS = bitrange.applyInverse(evaldRHS);
			evaldLHS = bitrange.getOperand();
			
			//logger.debug("Result: " + evaldLHS + " :=" + evaldBitWidth + "= " + evaldRHS);
		}

		RTLStatement newStmt;
		
		// Now make this a proper assignment to either variable or memory				
		if (evaldLHS instanceof RTLVariable) {
			newStmt = new RTLVariableAssignment(bitWidth, (RTLVariable)evaldLHS, evaldRHS);
		} else if (evaldLHS instanceof RTLMemoryLocation) {
			newStmt = new RTLMemoryAssignment((RTLMemoryLocation)evaldLHS, evaldRHS);
		} else {
			throw new RuntimeException("Lefthandside of assignment is neither variable nor memory after instantiation.");
		}
		
		// Make sure the statement is labeled
		newStmt.setLabel(getLabel());
		newStmt.setNextLabel(getNextLabel());
		return newStmt;
	}
	
	public int getBitWidth() {
		return bitWidth;
	}

	public Writable getLeftHandSide() {
		return leftHandSide;
	}

	public RTLExpression getRightHandSide() {
		return rightHandSide;
	}

	@Override
	public void inferTypes(Architecture arch) throws TypeInferenceException {
		leftHandSide = (Writable)(leftHandSide.inferBitWidth(arch, bitWidth));
		rightHandSide = rightHandSide.inferBitWidth(arch, bitWidth);
	}

	@Override
	public String toString() {
		StringBuilder res = new StringBuilder(255);

		res.append(leftHandSide);
		res.append(" := ");
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
		throw new UnsupportedOperationException("Assignment templates do not support visitors");
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + bitWidth;
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
		AssignmentTemplate other = (AssignmentTemplate) obj;
		if (bitWidth != other.bitWidth)
			return false;
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
