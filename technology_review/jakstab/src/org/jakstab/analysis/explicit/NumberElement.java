/*
 * NumberElement.java - This file is part of the Jakstab project.
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

import java.util.Collections;
import java.util.Set;

import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.rtl.BitVectorType;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.*;

/**
 * @author Johannes Kinder
 */
public class NumberElement implements AbstractValue, BitVectorType {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(NumberElement.class);
	
	public static final NumberElement TRUE = new NumberElement(ExpressionFactory.TRUE);
	public static final NumberElement FALSE = new NumberElement(ExpressionFactory.FALSE);
	
	private static NumberElement[] TOPS = new NumberElement[128];
	static {
		for (int bitWidth = 1; bitWidth <= 128; bitWidth++) {
			TOPS[bitWidth - 1] = new NumberElement(ExpressionFactory.createNumber(bitWidth - 1, bitWidth)); 
		}
	}
	
	public static NumberElement getTop(int bitWidth) {
		return TOPS[bitWidth - 1];
	}

	private final RTLNumber value;
	
	public NumberElement(RTLNumber v) {
		this.value = v;
		assert v.getBitWidth() > 0 : "Cannot create number element for " + v + " with unknown bitwidth!";
		assert value != null;
	}
	
	public RTLNumber getNumber() {
		assert !isTop() : "Attempting to get value of a TOP NumberElement!";
		return value;
	}
	
	@Override
	public Set<RTLNumber> concretize() {
		if (isTop()) {
			// Enumerate small bitwidths
			if (getBitWidth() == 1) {
				Set<RTLNumber> result = new FastSet<RTLNumber>();
				result.add(ExpressionFactory.TRUE);
				result.add(ExpressionFactory.FALSE);
				return result;
			} else {
				return RTLNumber.ALL_NUMBERS;
			}
		}
		return Collections.singleton(value);
	}

	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public boolean isTop() {
		return this == getTop(getBitWidth());
	}
	
	@Override
	public int getBitWidth() {
		return value.getBitWidth();
	}

	@Override
	public NumberElement join(LatticeElement l) {
		NumberElement other = (NumberElement)l;

		// Can happen for memory cells at same offset but of different size
		//assert other.getBitWidth() == this.getBitWidth() : "Trying to join numberelements of different bitwidth: " + other + " and " + this;
		if (other.getBitWidth() > this.getBitWidth()) return getTop(other.getBitWidth()); 
		if (this.getBitWidth() > other.getBitWidth()) return getTop(this.getBitWidth()); 
		if (l.isTop() || isTop()) return getTop(getBitWidth());
		
		RTLNumber c = other.value;
		if (c.equals(value)) return this;
		else return getTop(getBitWidth());
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		return l.isTop() || equals(l);
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj == this) return true;
		if (!(obj instanceof NumberElement)) return false;
		NumberElement other = (NumberElement)obj;
		if (getBitWidth() != other.getBitWidth()) return false;
		if (isTop()) return other.isTop();
		return other.value.equals(this.value);
	}

	@Override
	public int hashCode() {
		return value.intValue();
		// intValue is slightly faster than hashCode - and this is a hotspot
		//return value.hashCode();
	}

	@Override
	public String toString() {
		if (isTop()) return Characters.TOP + "<" + getBitWidth() + ">";
		else return value.toString();
	}

	@Override
	public boolean hasUniqueConcretization() {
		return !isTop() && !isBot();
	}
}
