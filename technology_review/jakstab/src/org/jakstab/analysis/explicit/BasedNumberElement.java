/*
 * BasedNumberElement.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.explicit;

import java.util.*;

import org.jakstab.Program;
import org.jakstab.analysis.*;
import org.jakstab.rtl.BitVectorType;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Characters;
import org.jakstab.util.Logger;

/**
 * Represents symbolic constants of the form "region + offset". Used
 * for representing variable memory addresses of stack and heap structures.
 * Non-address values are identified with the "global" region.
 * 
 * @author Johannes Kinder
 */
public class BasedNumberElement implements AbstractDomainElement, BitVectorType {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(BasedNumberElement.class);
	
	private static BasedNumberElement[] TOPS = new BasedNumberElement[128];
	static {
		for (int bitWidth = 1; bitWidth <= 128; bitWidth++) {
			TOPS[bitWidth - 1] = new BasedNumberElement(MemoryRegion.TOP, NumberElement.getTop(bitWidth)); 
		}
	}

	public static final BasedNumberElement TRUE = new BasedNumberElement(MemoryRegion.GLOBAL, NumberElement.TRUE);
	public static final BasedNumberElement FALSE = new BasedNumberElement(MemoryRegion.GLOBAL, NumberElement.FALSE);
	
	public static BasedNumberElement getTop(int bitWidth) {
		return TOPS[bitWidth - 1];
	}
	
	private final MemoryRegion region;
	private final NumberElement value;
	
	public BasedNumberElement(MemoryRegion region, NumberElement value) {
		this.region = region;
		this.value = value;
		assert value != null;
		assert region != null;
		if (!region.isBot() && !region.isTop() && value.getBitWidth() != Program.getProgram().getArchitecture().getAddressBitWidth())
			logger.verbose("Created based number element " + this + " with non-address-sized bitwidth!");
	}
		
	public BasedNumberElement(MemoryRegion region, RTLNumber number) {
		this(region, new NumberElement(number));
	}
	
	public BasedNumberElement(RTLNumber v) {
		this(MemoryRegion.GLOBAL, new NumberElement(v));
	}
	
	public boolean isNumberTop() {
		assert (!isTop()) : "TOP BasedNumberElement has no number!";
		return value.isTop();
	}
	
	public RTLNumber getNumber() {
		return value.getNumber();
	}

	@Override
	public Set<RTLNumber> concretize() {
		// Just pass down to number elements - value in TOPs are 
		// corresponding NumerElement TOPs
		return value.concretize();
	}

	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public boolean isTop() {
		return region == MemoryRegion.TOP && value.isTop();
	}
	
	@Override
	public int getBitWidth() {
		// Top and unbased values carry the bitwidth in their NumberElements
		//if (isTop() || isUnbased()) return value.getBitWidth();
		//
		// All based numbers are addresses
		// FS is a 16bit register but stores a region-address (FS:0), so we cannot
		// just return 32 bit for all region-addresses. 
		//return Program.getProgram().getArchitecture().getAddressBitWidth();
		return value.getBitWidth();
	}
	
	public boolean isUnbased() {
		return region == MemoryRegion.GLOBAL;
	}
	
	/**
	 * Checks whether this element represents just a single concrete value.
	 * 
	 * @return True if this abstract element's concretization has exactly one concrete element.
	 */
	public boolean hasUniqueConcretization() {
		return !isTop() && isUnbased() && !isNumberTop();
	}

	@Override
	public BasedNumberElement join(LatticeElement l) {
		BasedNumberElement other = (BasedNumberElement)l;
		// Can happen for memory cells at same offset but of different size - no it shouldn't!
		assert other.getBitWidth() == this.getBitWidth() : "Different bitwidths: " + other + " with " + other.getBitWidth() + " and " + this + " with " + this.getBitWidth();
		//if (other.getBitWidth() > this.getBitWidth()) return getTop(other.getBitWidth()); 
		//if (this.getBitWidth() > other.getBitWidth()) return getTop(this.getBitWidth()); 
		if (other.isTop()) return other;
		if (isTop()) return this;
		if (equals(other)) return this;

		if (region != other.region) return getTop(getBitWidth());
		else return new BasedNumberElement(region, value.join(other.value));
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		if (l.isTop() || equals(l)) return true;
		if (isTop()) return l.isTop();
		BasedNumberElement other = (BasedNumberElement)l;
		return region == other.region && value.lessOrEqual(other.value);
	}
	
	@Override
	public int hashCode() {
		return region.hashCode() * 31 + value.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		BasedNumberElement other = (BasedNumberElement) obj;
		return region.equals(other.region) && value.equals(other.value);
	}

	@Override
	public String toString() {
		if (isTop()) return Characters.TOP + "<" + getBitWidth() + ">";
		else if (region == MemoryRegion.GLOBAL) return "$" + value.toString();
		else return region.toString() + "+" + value.toString();
	}

	public MemoryRegion getRegion() {
		return region;
	}

	@Override
	public BasedNumberElement bitExtract(int first, int last) {
		if (getRegion() != MemoryRegion.GLOBAL) 
			return getTop(getBitWidth());
		else 
			return new BasedNumberElement(getRegion(), getNumber().bitExtract(first, last));
	}

	@Override
	public BasedNumberElement multiply(AbstractDomainElement op) {
		BasedNumberElement other = (BasedNumberElement)op;
		if (other.getRegion() != MemoryRegion.GLOBAL || getRegion() != MemoryRegion.GLOBAL ) {
			return getTop(Math.max(getBitWidth(), other.getBitWidth()));
		}
		return new BasedNumberElement(getRegion(), getNumber().multiply(other.getNumber()));
	}

	@Override
	public BasedNumberElement negate() {
		if (region != MemoryRegion.GLOBAL) 
			return getTop(getBitWidth());
		else 
			return new BasedNumberElement(getRegion(), getNumber().negate());
	}

	@Override
	public BasedNumberElement plus(AbstractDomainElement op) {
		BasedNumberElement other = (BasedNumberElement)op;
		
		MemoryRegion resultRegion = region.join(other.getRegion());
		
		if (resultRegion != MemoryRegion.TOP) {
			return new BasedNumberElement(resultRegion, getNumber().plus(other.getNumber()));
		} else {
			return getTop(Math.max(getBitWidth(), other.getBitWidth()));
		}
	}

	@Override
	public BasedNumberElement readStore(int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		return (BasedNumberElement)store.get(getRegion(), getNumber().longValue(), bitWidth);
	}

	@Override
	public Collection<BasedNumberElement> readStorePowerSet(
			int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		return Collections.singleton(readStore(bitWidth, store));
	}

	@Override
	public <A extends AbstractDomainElement> void writeStore(int bitWidth,
			PartitionedMemory<A> store, A value) {
		if (isTop()) 
			store.setTop();
		else if (isNumberTop()) 
			store.setTop(getRegion());
		else 
			store.set(getRegion(), getNumber().longValue(), bitWidth, value);
	}

	@Override
	public BasedNumberElement signExtend(int first, int last) {
		if (region != MemoryRegion.GLOBAL) 
			return getTop(getBitWidth());
		else 
			return new BasedNumberElement(getRegion(), getNumber().signExtend(first, last));
	}

	@Override
	public BasedNumberElement zeroFill(int first, int last) {
		if (region != MemoryRegion.GLOBAL) 
			return getTop(getBitWidth());
		else 
			return new BasedNumberElement(getRegion(), getNumber().zeroFill(first, last));
	}
}
