/*
 * RTLSpecialExpression.java - This file is part of the Jakstab project.
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

import java.util.Arrays;
import java.util.Set;

import org.jakstab.rtl.*;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * "Special" expressions which are not (yet) supported in RTLOperation.
 * 
 * @author Johannes Kinder
 */
public class RTLSpecialExpression extends AbstractRTLExpression implements RTLExpression  {
	
	public static final String FTRUNC = "ftrunc";
	public static final String LOG2 = "log2";
	public static final String TICKCOUNT = "tickcount";
	public static final String GETPROCADDRESS = "getProcAddress";
	public static final String DBG_PRINTF = "dbgPrintf";
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLSpecialExpression.class);
	protected Set<RTLMemoryLocation> usedMemoryLocations = null;

	private final String operation;
	private final RTLExpression[] operands;
	private final int operandCount;
	private final int size;
	private final int bitWidth;
	
	protected RTLSpecialExpression(String operation, RTLExpression... operands) {
		super();
		this.operation = operation;
		if (operation.equals(TICKCOUNT)) bitWidth = 64;
		else if (operation.equals(GETPROCADDRESS)) bitWidth = 32;
		else if (operation.equals(DBG_PRINTF)) bitWidth = 32;
		else {
			// Everything else is floating point stuff anyway
			bitWidth = 80;
			//logger.warn("Unsupported special expression: " + operation);
		}
		
		if (operands == null || operands.length == 0 || operands[0] == null ) {
			this.operandCount = 0;
			this.operands = null;
			this.size = 1;
		} else {
			this.operands = operands;
			int opCount = operands.length;
			int theSize = 1;
			// See if it's actually less real operands
			for (int i=0; i < operands.length; i++)
				if (operands[i] == null) {
					opCount = i;
					break;
				} else theSize += operands[i].size();
			this.operandCount = opCount;
			this.size = theSize;
		}
	}

	/**
	 * @return the operation
	 */
	public String getOperator() {
		return operation;
	}
	
	/**
	 * @return the operands
	 */
	public RTLExpression[] getOperands() {
		return operands;
	}

	public int getOperandCount() {
		return operandCount;
	}

	/*
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (obj == null || obj.getClass() != this.getClass()) return false;
		RTLSpecialExpression other = (RTLSpecialExpression)obj;
		return other.operation.equals(this.operation) && Arrays.equals(this.operands, other.operands);
	}

	/*
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return 7 + operation.hashCode() + Arrays.hashCode(operands);
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		if (operandCount == 0) return operation.toString();
		StringBuilder res = new StringBuilder();
		res.append(operation.toString() + "(");
		res.append(operands[0].toString());
		for (int i = 1; i < operandCount; i++)
			res.append(", " + operands[i].toString());
		res.append(')');
		return res.toString();
	}

	@Override
	public RTLExpression evaluate(Context context) {
		RTLExpression[] evaledOperands = new RTLExpression[operandCount]; 
		for(int i=0; i<operandCount; i++)
			evaledOperands[i] = operands[i].evaluate(context);

		return ExpressionFactory.createSpecialExpression(operation, evaledOperands);
	}
	
	@Override
	public SetOfVariables getUsedVariables() {
		if (usedVariables == null) {
			usedVariables = new SetOfVariables();
			for(int i=0; i<operandCount; i++) {
				usedVariables.addAll(operands[i].getUsedVariables());
			}
		}
		return usedVariables;
	}

	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocations() {
		if (usedMemoryLocations == null) {
			usedMemoryLocations = new FastSet<RTLMemoryLocation>();
			for(int i=0; i<operandCount; i++) {
				usedMemoryLocations.addAll(operands[i].getUsedMemoryLocations());
			}
		}
		return usedMemoryLocations;
	}

	@Override
	public int size() {
		return size;
	}
	
	@Override
	public int getBitWidth() {
		return bitWidth;
	}

	@Override
	public RTLExpression inferBitWidth(Architecture arch, int expectedBitWidth)
			throws TypeInferenceException {
		// TODO: implement this
		return this;
	}
	
	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
