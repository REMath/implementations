/*
 * RTLBitrange.java - This file is part of the Jakstab project.
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

import java.util.Set;

import org.jakstab.rtl.Context;
import org.jakstab.rtl.TypeInferenceException;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;

/**
 * A bitrange over another expression. Both start and endbits can be expressions, but the 
 * bitwidth can only be determined if start and end position are numbers. 
 * 
 * @author Johannes Kinder
 */
public class RTLBitRange extends AbstractRTLExpression implements RTLExpression, Writable {

	/**
	 * Creates a Bitmask in which all bits from startbit to and including
	 * endbit are set.
	 * 
	 * @param startBit The positive index of the first bit to set 
	 * @param endBit The positive index of the last bit to set
	 * @return The bitmask
	 */
	public final static long bitMask(int startBit, int endBit) {
		return ((1L << (endBit - startBit + 1) ) - 1) << startBit;
	}

	public static final RTLNumber calculate(RTLNumber firstIndex, RTLNumber lastIndex, RTLNumber operand) {
		int firstBit = firstIndex.intValue();
		int lastBit = lastIndex.intValue();
		return calculate(firstBit, lastBit, operand);
	}
	
	public static final RTLNumber calculate(int firstBit, int lastBit, RTLNumber operand) {
		long value = operand.longValue();
		return ExpressionFactory.createNumber((bitMask(firstBit, lastBit) & value) >> firstBit, 
				lastBit - firstBit + 1);
	}

	private final static Logger logger = Logger.getLogger(RTLBitRange.class);

	private final RTLExpression firstBit;
	private final RTLExpression lastBit;
	private final RTLExpression operand;
	private final int size;
	private SetOfVariables usedVariablesOnWrite = null;

	protected RTLBitRange(RTLExpression variable, RTLExpression firstBit, RTLExpression lastBit) {
		super();
		this.operand = variable;
		this.firstBit = firstBit;
		this.lastBit = lastBit;
		this.size = 1 + operand.size() + firstBit.size() + lastBit.size();
	}
	
	@Override
	public RTLExpression evaluate(Context context) {
		RTLExpression evaldOperand = operand.evaluate(context);
		RTLExpression evaldFirstBit = firstBit.evaluate(context);
		RTLExpression evaldLastBit = lastBit.evaluate(context);

		if (evaldFirstBit instanceof RTLNumber && evaldLastBit instanceof RTLNumber) {
			int firstBit = ((RTLNumber)evaldFirstBit).intValue();
			int lastBit = ((RTLNumber)evaldLastBit).intValue();
			// Check for unnecessary index
			if (firstBit == 0 && evaldOperand instanceof RTLVariable && 
					((RTLVariable)evaldOperand).getBitWidth() == lastBit + 1) {
				logger.debug("Removing unnecessary Bitrange from " + this.toString());
				return evaldOperand;
			}
			if (evaldOperand instanceof RTLNumber) {
				//long value = ((RTLNumber)evaldOperand).longValue();
				//return ExpressionFactory.createNumber((bitMask(firstBit, lastBit) & value) >> firstBit, 
				//		lastBit - firstBit + 1);
				return calculate((RTLNumber)evaldFirstBit, (RTLNumber)evaldLastBit, (RTLNumber)evaldOperand);
			}
		}
		return ExpressionFactory.createBitRange(evaldOperand, evaldFirstBit, evaldLastBit);
	}

	@Override
	public SetOfVariables getDefinedVariablesOnWrite() {
		if (operand instanceof Writable) 
			return ((Writable)operand).getDefinedVariablesOnWrite();
		else
			throw new RuntimeException("Non-writable operand in bitrange!");
			//return operand.getUsedVariables();
	}

	/**
	 * @return the firstBit
	 */
	public RTLExpression getFirstBitIndex() {
		return firstBit;
	}

	/**
	 * @return the lastBit
	 */
	public RTLExpression getLastBitIndex() {
		return lastBit;
	}

	/**
	 * @return the operand
	 */
	public RTLExpression getOperand() {
		return operand;
	}
	
	/**
	 * Creates a bitmasking expression over the supplied parameter that is the
	 * inverse of this bitrange. Can be used for simplifying assignments such as
	 * x[0:7] = y; to x := (x & bitmask) | (size of x)y;
	 * x[8:15] = y; to x := (x & bitmask) | ((size of x)y << 8)
	 *  
	 * @param rhs the expression that the inverse should be applied to
	 * @return The inverse of this bitrange applied to the parameter
	 */
	public RTLExpression applyInverse(RTLExpression rhs) {
		int firstBit = ((RTLNumber)getFirstBitIndex()).intValue();
		int lastBit = ((RTLNumber)getLastBitIndex()).intValue();
		long bitMask = RTLBitRange.bitMask(0, firstBit - 1) | 
			RTLBitRange.bitMask(lastBit + 1, operand.getBitWidth());

		// Bring rhs up to the size of the operand
		RTLExpression castToOpSize = ExpressionFactory.createZeroFill( 
				ExpressionFactory.createNumber(rhs.getBitWidth(), 8),
				ExpressionFactory.createNumber(getOperand().getBitWidth() - 1, 8),
				rhs
		);

		// Shift rhs if necessary
		RTLExpression maskedRhs;
		if (firstBit == 0) {
			maskedRhs = castToOpSize;
		} else {
			maskedRhs =	ExpressionFactory.createShiftLeft(
					castToOpSize,
					getFirstBitIndex()
			);
		}

		// Create the mask
		RTLExpression ret = ExpressionFactory.createOr(
				ExpressionFactory.createAnd(
						getOperand(), 
						ExpressionFactory.createNumber(bitMask, getOperand().getBitWidth())
				), maskedRhs
		);
		
		//logger.debug("Created " + ret);
		return ret;
	}

	@Override
	public SetOfVariables getUsedVariables() {
		if (usedVariables == null) {
			usedVariables = new SetOfVariables();
			if (firstBit != null) usedVariables.addAll(firstBit.getUsedVariables());
			if (lastBit != null) usedVariables.addAll(lastBit.getUsedVariables());
			if (operand != null) usedVariables.addAll(operand.getUsedVariables());
		}
		return usedVariables;
	}
	
	@Override
	public SetOfVariables getUsedVariablesOnWrite() {
		if (usedVariablesOnWrite == null) {
			usedVariablesOnWrite = new SetOfVariables();
			if (firstBit != null) usedVariablesOnWrite.addAll(firstBit.getUsedVariables());
			if (lastBit != null) usedVariablesOnWrite.addAll(lastBit.getUsedVariables());
			// This was a temp fix for AH, AL etc.
			// usedVariablesOnWrite.addAll(operand.getUsedVariables());
		}
		return usedVariablesOnWrite;
	}
	
	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocations() {
		return operand.getUsedMemoryLocations();
	}
	
	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocationsOnWrite() {
		if (operand instanceof Writable) 
			return ((Writable)operand).getUsedMemoryLocationsOnWrite();
		else
			throw new RuntimeException("Non-writable operand in bitrange!");
			//return operand.getUsedVariables();
	}

	@Override
	public Set<RTLMemoryLocation> getDefinedMemoryLocationsOnWrite() {
		if (operand instanceof Writable) 
			return ((Writable)operand).getDefinedMemoryLocationsOnWrite();
		else
			throw new RuntimeException("Non-writable operand in bitrange!");
			//return operand.getUsedVariables();
	}

	@Override
	public String toString() {
		String bitRange;
		if (firstBit instanceof RTLNumber && lastBit instanceof RTLNumber) {
			int first = ((RTLNumber)firstBit).intValue();
			int last = ((RTLNumber)lastBit).intValue();
			if (first == last)
				bitRange = Integer.toString(first);
			else
				bitRange = first + ":" + last;
		} else {
			bitRange = firstBit.toString() + ":" + lastBit.toString();
		}
		return operand.toString() +	"@[" + bitRange + "]";
	}

	@Override
	public int getBitWidth() {
		if (firstBit instanceof RTLNumber && lastBit instanceof RTLNumber) {
			int result = ((RTLNumber)lastBit).intValue() - ((RTLNumber)firstBit).intValue() + 1;
			return result;
		} else {
			if (firstBit.equals(lastBit)) return 1;
			assert false : "Cannot determine bitwidth for bitrange from " + firstBit + " to " + lastBit;
			return -1;
		}
	}

	@Override
	public int size() {
		return size;
	}

	/*
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (obj == null || obj.getClass() != this.getClass()) return false;
		RTLBitRange other = (RTLBitRange)obj;
		return  other.operand.equals(this.operand) && 
		other.firstBit.equals(this.firstBit) && 
		other.lastBit.equals(this.lastBit);
	}

	/*
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return 3 + firstBit.hashCode() + lastBit.hashCode() + operand.hashCode();
	}

	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}

	/*
	 * @see org.jakstab.rtl.expressions.AbstractRTLExpression#inferBitWidth(org.jakstab.ssl.Architecture, int)
	 */
	@Override
	public RTLExpression inferBitWidth(Architecture arch, int expectedBitWidth)
			throws TypeInferenceException {
		super.inferBitWidth(arch, expectedBitWidth);
		// Try to make bit indices 8 bit, if it fails, leave them the way they are
		RTLExpression typedFirstBit; 
		try {
			typedFirstBit = firstBit.inferBitWidth(arch, 8);
		} catch (TypeInferenceException e) {
			logger.warn("Exception on inferring type of first bit index " + firstBit);
			typedFirstBit = firstBit;
		}
		RTLExpression typedLastBit;
		try {
			typedLastBit = lastBit.inferBitWidth(arch, 8);
		} catch (TypeInferenceException e) {
			logger.warn("Exception on inferring type of last bit index " + lastBit);
			typedLastBit = lastBit;
		}
		return ExpressionFactory.createBitRange(operand, typedFirstBit, typedLastBit);
	}
	
	
}
