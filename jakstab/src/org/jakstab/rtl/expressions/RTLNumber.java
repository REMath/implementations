/*
 * RTLNumber.java - This file is part of the Jakstab project.
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

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import org.jakstab.analysis.*;
import org.jakstab.rtl.*;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.Logger;

/**
 * Wrapper class for representing integer numbers with a defined number of bits.
 * 
 * @author Johannes Kinder
 */
public class RTLNumber extends AbstractRTLExpression implements RTLExpression, AbstractDomainElement {

	public static final RTLNumber WILDCARD = null;
	public static final Set<RTLNumber> ALL_NUMBERS = Collections.singleton(WILDCARD);
	
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(RTLNumber.class);
	private final int bitWidth;
	private final long value;

	protected RTLNumber(long value, int bitWidth) {
		super();
		
		this.bitWidth = bitWidth;
		
		// Implements bitvector semantics by wrapping all created numbers 
		// according to bitwidth
		if (bitWidth < 64 && bitWidth > 1) {
			value = value % (1L << bitWidth);
			if (value >= (1L << (bitWidth - 1))) {
				value = value - (1L << bitWidth);
			}
			else if (value < -(1L << (bitWidth - 1))) {
				value = value + (1L << bitWidth);
			}
		}
		this.value = value;
		
		assert this.bitWidth != 1 || this.value == 0L || this.value == -1L;
	}

	/**
	 * @return the represented number cast to an integer.
	 */
	public int intValue() {
		return (int)value;
	}
	
	/**
	 *  
	 * @return the represented number as long integer.
	 */
	public long longValue() {
		return value;
	}

	/*
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (obj == null || obj.getClass() != this.getClass()) 
			return false;
		RTLNumber other = ((RTLNumber)obj);
		// If one is weakly typed, only check values
		/*if (bitWidth == RTLVariable.UNKNOWN_BITWIDTH || other.bitWidth == RTLVariable.UNKNOWN_BITWIDTH)
			return other.value == value;*/
		return other.value == value && other.bitWidth == bitWidth;
	}

	/*
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return 83 + (int)value + bitWidth;
	}

	/*
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		if (bitWidth == 1) {
			return (value == 0L) ? "false" : "true";
		}
		//String bw = "<" + (bitWidth==RTLVariable.UNKNOWN_BITWIDTH ? "?" : bitWidth) + ">";
		return Long.toString(value); //+ bw;
	}
	
	@Override
	public String toHexString() {
		String bw = "<" + (bitWidth==RTLVariable.UNKNOWN_BITWIDTH ? "?" : bitWidth) + ">";
		String hex = Integer.toHexString((int)value);
		if (value < 0 && bitWidth > 0) {
			hex = hex.substring(Math.max(0, hex.length() - (bitWidth / 4)));
		}
		return "0x" + hex + bw;
	}

	@Override
	public RTLExpression evaluate(Context context) {
		return this;
	}

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

	@Override
	public int getBitWidth() {
		return bitWidth;
	}

	@Override
	public RTLExpression inferBitWidth(Architecture arch, int expectedBitWidth) throws TypeInferenceException {
		if (bitWidth == expectedBitWidth) return this;
		else if (bitWidth <= 0) {
			// Does the value (signed) fit into the bits? 
			if (Math.log(Math.abs(value)) / Math.log(2) <= (expectedBitWidth - 1))
				return ExpressionFactory.createNumber(this.value, expectedBitWidth);
			else throw new TypeInferenceException("Expected bit width of " + 
					expectedBitWidth + " too small to hold numeric value of " + value + "!"); 
		} else if (bitWidth < expectedBitWidth) {
			// TODO: Check if sign extension is correct
			return ExpressionFactory.createNumber(value, expectedBitWidth);
		} else {
			// Expected bitwidth less than our bitwidth
			throw new TypeInferenceException(this.toString() + " expected to be of bitwidth " + expectedBitWidth);
		}
	}
	
	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}

	@Override
	public RTLNumber bitExtract(int first, int last) {
		return RTLBitRange.calculate(first, last, this);
	}

	@Override
	public RTLNumber join(LatticeElement l) {
		return null;
	}

	@Override
	public RTLNumber multiply(AbstractDomainElement op) {
		RTLNumber other = (RTLNumber)op;
		return ExpressionFactory.createNumber(
				value * other.value, Math.max(bitWidth, other.bitWidth));
	}

	@Override
	public RTLNumber negate() {
		return ExpressionFactory.createNumber(-value, bitWidth);
	}

	@Override
	public RTLNumber plus(AbstractDomainElement op) {
		RTLNumber other = (RTLNumber)op;
		return ExpressionFactory.createNumber(
				value + other.value, Math.max(bitWidth, other.bitWidth));
	}

	@Override
	public RTLNumber readStore(int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		return (RTLNumber)store.get(MemoryRegion.GLOBAL, value, bitWidth);
	}

	@Override
	public Collection<RTLNumber> readStorePowerSet(
			int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		return Collections.singleton(readStore(bitWidth, store));
	}
	
	@Override
	public <A extends AbstractDomainElement> void writeStore(int bitWidth,
			PartitionedMemory<A> store,
			A valueToWrite) {
		store.set(MemoryRegion.GLOBAL, value, bitWidth, valueToWrite);
	}

	@Override
	public RTLNumber signExtend(int first, int last) {
		int targetWidth = Math.max(bitWidth, last + 1);
		long extension = value;
		if ((value & RTLBitRange.bitMask(bitWidth - 1,  bitWidth - 1)) > 0) {
			extension = value | RTLBitRange.bitMask(first, last);
		}
		return ExpressionFactory.createNumber(extension, targetWidth);
	}

	@Override
	public RTLNumber zeroFill(int first, int last) {
		int targetWidth = Math.max(bitWidth, last + 1);
		long filled = value & (
				RTLBitRange.bitMask(0, first - 1) |
				RTLBitRange.bitMask(last + 1, targetWidth - 1));
		return ExpressionFactory.createNumber(filled, targetWidth);
	}

	@Override
	public Set<RTLNumber> concretize() {
		return Collections.singleton(this);
	}

	@Override
	public boolean hasUniqueConcretization() {
		return true;
	}

	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public boolean isTop() {
		return false;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		return equals(l);
	}
}
