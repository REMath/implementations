/*
 * Copyright 2002 Sun Microsystems, Inc.  All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
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
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Sun Microsystems, Inc., 4150 Network Circle, Santa Clara,
 * CA 95054 USA or visit www.sun.com if you need additional information or
 * have any questions.
 *  
 */

/* 
 * Original code for this class taken from the Java HotSpot VM. 
 * Modified for use with the Jakstab project. All modifications 
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 */

package org.jakstab.asm;

/**
 * A memory operand pointed to by a Base Index Scale Displacement address.
 * The effective address of the operand is calculated as 
 * (base + (index * scale) + displacement).
 * Optionally, the index is auto incremented or decremented.
 */
public abstract class MemoryOperand extends Operand {
	private final DataType dataType;
	private final Register base, index;
	private final int      scale;
	private final long     disp;
	private boolean  autoIncr;
	private boolean  autoDecr;

	public MemoryOperand(DataType dataType, Register base, Register index, long disp, int scale) {
		this.dataType = dataType;
		this.base = base;
		this.index = index;
		this.disp = disp;
		this.scale = scale;
	}

	public MemoryOperand(DataType dataType, Register base, Register index, long disp) {
		this(dataType, base, index, disp, 1);
	}

	public MemoryOperand(DataType dataType, Register base, Register index) {
		this(dataType, base, index, 0L, 1);
	}

	public MemoryOperand(DataType dataType, Register base, long disp) {
		this(dataType, base, null, disp, 1);
	}

	public Register getBase() {
		return base;
	}

	public Register getIndex() {
		return index;
	}

	public int getScale() {
		return scale;
	}

	public long getDisplacement() {
		return disp;
	}
	
	/**
	 * @return the dataType
	 */
	public DataType getDataType() {
		return dataType;
	}

	/**
	 * Returns whether the index is automatically incremented. 
	 */
	public boolean isAutoIncrement() {
		return autoIncr;
	}

	public void setAutoIncrement(boolean value) {
		autoIncr = value;
	}

	/**
	 * Returns whether the index is automatically decremented. 
	 */
	public boolean isAutoDecrement() {
		return autoDecr;
	}

	public void setAutoDecrement(boolean value) {
		autoDecr = value;
	}

//	public long getEffectiveValue(long pcValue) {
//		if (base == null && index == null && scale <= 1)
//			return getDisplacement();
//		else return -1L;
//	}

}
