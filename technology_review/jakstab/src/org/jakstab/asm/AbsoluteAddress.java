/*
 * AbsoluteAddress.java - This file is part of the Jakstab project.
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

package org.jakstab.asm;

import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLNumber;


public class AbsoluteAddress extends Address implements Comparable<AbsoluteAddress> {

	protected final long value;

	public AbsoluteAddress(long value) {
		this.value = value;
	}
	
	public AbsoluteAddress(RTLNumber c) {
		switch (c.getBitWidth()) {
		case 16:
			this.value = 0xFFFFL & c.longValue();
			break;
		case 32:
			this.value = 0xFFFFFFFFL & c.longValue();
			break;
		default:
			this.value = c.longValue();
		}
	}
	
	public RTLNumber toNumericConstant() {
		return ExpressionFactory.createNumber(value, getBitWidth());
	}

	@Override
	public int compareTo(AbsoluteAddress o) {
		if (value < o.value) return -1;
		if (value > o.value) return 1;
		return 0;
	}
	
	@Override
	public long getEffectiveValue(long pcValue) {
		return getValue();
	}

	public long getValue() {
		return value;
	}

	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer(10);
		sb.append("0x");
		sb.append(String.format("%08x", value));
		return sb.toString();
	}

	/*
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (int) (value ^ (value >>> 32));
		return result;
	}

	/*
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		AbsoluteAddress other = (AbsoluteAddress) obj;
		if (value != other.value)
			return false;
		return true;
	}
}
