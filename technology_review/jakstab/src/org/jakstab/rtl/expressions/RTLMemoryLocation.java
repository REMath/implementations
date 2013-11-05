/*
 * RTLMemoryLocation.java - This file is part of the Jakstab project.
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

import org.jakstab.rtl.*;
import org.jakstab.ssl.Architecture;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * A memory location with a specified data type/bit width and an address defined by another 
 * expression. IA-32 addresses can also contain a segment register, but the implementation
 * is not yet complete.
 * 
 * @author Johannes Kinder
 */
public class RTLMemoryLocation extends AbstractRTLExpression implements RTLExpression, Writable {

	@SuppressWarnings("unused")
	private final static Logger logger = Logger.getLogger(RTLMemoryLocation.class);
			
	private Set<RTLMemoryLocation> usedMemoryLocations = null;
	private SetOfVariables usedVariablesOnWrite;
	private final RTLExpression segmentRegister;
	private final RTLExpression address;
	private final int bitWidth;
	private final int size;
	private final int memoryState;

	protected RTLMemoryLocation(int memoryState, RTLExpression segmentRegister, RTLExpression address, int bitWidth) {
		super();
		this.memoryState = memoryState;
		this.address = address;
		this.segmentRegister = segmentRegister;
		this.bitWidth = bitWidth;
		this.size = 1 + (address != null ? address.size() : 0 ) 
				+ (segmentRegister != null ? segmentRegister.size() : 0 );
	}

	/**
	 * @return the address
	 */
	public RTLExpression getAddress() {
		return address;
	}

	public int getBitWidth() {
		return bitWidth;
	}

	/**
	 * @return the segment register for this memory access, if specified,
	 *         otherwise null.
	 */
	public RTLExpression getSegmentRegister() {
		return segmentRegister;
	}

	/**
	 * Return the logical state this memory location refers to. Usually 0, but can
	 * be higher to allow expressions to refer to different memory states, e.g. as in
	 * mem32'[10] = mem32[10] + 5; 
	 * 
	 * @return the memory state (number of 'primes')
	 */
	public int getMemoryState() {
		return memoryState;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		//if (getUsedVariables().contains(ExpressionFactory.getInstance().stackPointer))
		//		sb.append("stack");
		//else 
		sb.append("mem");
		if (bitWidth > 0) sb.append(bitWidth);
		for (int i = 0; i < memoryState; i++)
			sb.append('\'');
		sb.append("[");
		if (segmentRegister != null) {
			sb.append(segmentRegister.toString());
			sb.append(":");
		}
		sb.append(address.toHexString());
		sb.append("]");
		return sb.toString();
	}

	@Override
	public RTLExpression evaluate(Context context) {
		RTLExpression subst = context.getSubstitution(this);
		if (subst instanceof RTLMemoryLocation) {
			RTLMemoryLocation m = (RTLMemoryLocation)subst;
			RTLExpression evaldAddress = m.address.evaluate(context);
			RTLMemoryLocation evaldMemLoc = evaldAddress == m.address ? 
					m : ExpressionFactory.createMemoryLocation(m.segmentRegister, evaldAddress, m.bitWidth);

			RTLExpression value = context.getAssignment(evaldMemLoc);
			if (value != null)
				return value;
			else 
				return evaldMemLoc;
		} else {
			return subst.evaluate(context);
		}
	}

	@Override
	public SetOfVariables getUsedVariables() {
		if (usedVariables == null) {
			usedVariables = new SetOfVariables();
			if (segmentRegister != null) 
				usedVariables.addAll(segmentRegister.getUsedVariables());
			if (address != null)
				usedVariables.addAll(address.getUsedVariables());
			//usedVariables.add(this);
		}
		return usedVariables;
	}

	@Override
	public SetOfVariables getUsedVariablesOnWrite() {
		if (usedVariablesOnWrite == null) {
			usedVariablesOnWrite = new SetOfVariables();
			if (segmentRegister != null) 
				usedVariablesOnWrite.addAll(segmentRegister.getUsedVariables());
			if (address != null)
				usedVariablesOnWrite.addAll(address.getUsedVariables());
		}
		return usedVariablesOnWrite;
	}
	
	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocations() {
		if (usedMemoryLocations == null) {
			usedMemoryLocations = new FastSet<RTLMemoryLocation>();
			usedMemoryLocations.addAll(address.getUsedMemoryLocations());
			usedMemoryLocations.add(this);
		}
		return usedMemoryLocations;
	}
	
	@Override
	public Set<RTLMemoryLocation> getDefinedMemoryLocationsOnWrite() {
		return Collections.singleton(this);
	}

	@Override
	public Set<RTLMemoryLocation> getUsedMemoryLocationsOnWrite() {
		return address.getUsedMemoryLocations();
	}

	@Override
	public SetOfVariables getDefinedVariablesOnWrite() {
		//return setOfThis;
		return SetOfVariables.EMPTY_SET;
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
		RTLMemoryLocation other = (RTLMemoryLocation)obj;
		return other.address.equals(address) && 
		other.bitWidth == bitWidth && 
		other.memoryState == memoryState && 
		(other.segmentRegister == segmentRegister || 
				(segmentRegister != null && segmentRegister.equals(other.segmentRegister)));
	}

	/*
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return 59 + address.hashCode() + bitWidth;
	}

	@Override
	public RTLExpression inferBitWidth(Architecture arch, int expectedBitWidth)
			throws TypeInferenceException {
		if (bitWidth != expectedBitWidth)
			throw new TypeInferenceException("Expected bitwidth of " + expectedBitWidth + ", but memory reference is " + bitWidth + " bit.");
		
		//return this;
		// Inferring address bitwidth currently does not work b/c of multiplication.
		// For MUL instructions, bitwidth gets doubled, in index-scale addressing, there is an implicit truncation

		RTLExpression typedAddress = address.inferBitWidth(arch, arch.getAddressBitWidth());
		if (typedAddress != address)
			return ExpressionFactory.createMemoryLocation(
					this.segmentRegister, typedAddress, bitWidth);
		else return this;
	}
	
	@Override
	public <T> T accept(ExpressionVisitor<T> visitor) {
		return visitor.visit(this);
	}
}
