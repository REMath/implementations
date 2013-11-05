/*
 * Copyright 2003 Sun Microsystems, Inc.  All Rights Reserved.
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

package org.jakstab.asm.x86;

import org.jakstab.asm.DataType;
import org.jakstab.asm.MemoryOperand;
import org.jakstab.asm.SymbolFinder;

/**
 *  Represents a memory operand pointed to by Base Index Scale Displacement on x86.
 *  May actually be an absolute address if base and index are null.
 *  
 *  Changed for correct AT&T syntax by Johannes Kinder
 *
 */
public class X86MemoryOperand extends MemoryOperand {

	final private X86SegmentRegister segReg;

	/**
	 * @return the segment register of this memory operand, if specified. If
	 * 		   it is not specified, returns null.
	 */
	public X86SegmentRegister getSegmentRegister() {
		return segReg;
	}

	public X86MemoryOperand(DataType dataType, X86SegmentRegister segReg, X86Register base, X86Register index, long disp, int scale) {
		super(dataType, base, index, disp, 1 << scale);
		this.segReg = segReg;
	}

	public X86MemoryOperand(DataType dataType, X86SegmentRegister segReg, X86Register base, X86Register index, long disp) {
		this(dataType, segReg, base, index, disp, 0);
	}

	public X86MemoryOperand(DataType dataType, X86SegmentRegister segReg, X86Register base) {
		this(dataType, segReg, base, null, 0, 0);
	}

	public X86MemoryOperand(DataType dataType, X86SegmentRegister segReg, long disp) {
		this(dataType, segReg, null, null, disp, 0);
	}

	public X86MemoryOperand(DataType dataType, long disp) {
		this(dataType, null, null, null, disp, 0);
	}

	
	/* (non-Javadoc)
	 * @see org.jakstab.asm.Operand#toString(long, org.jakstab.asm.SymbolFinder)
	 */
	@Override
	public String toString(long currentPc, SymbolFinder symFinder) {
		if (getBase() == null && getIndex() == null && getSegmentRegister() == null)
			return symFinder.getSymbolFor(getDisplacement());
		else return toString();
	}

	@Override
	public String toString() {

		StringBuffer buf = new StringBuffer();
		org.jakstab.asm.Register base = getBase();
		org.jakstab.asm.Register index = getIndex();
		int scaleVal = getScale();

		if(segReg != null) {
			buf.append(segReg.toString());
			buf.append(":");
		}

		long disp = getDisplacement();
		if (disp != 0 || (base == null && index == null)) {
			if (disp > 0)
				buf.append("0x" + Long.toHexString(disp));
			else {
				buf.append(disp);
			}
		} 

		if( (base != null) || (index != null) || (scaleVal > 1) )
			buf.append('(');

		if (base != null) buf.append(base.toString());
		if (index != null || scaleVal > 1 ) buf.append(',');
		if (index != null) buf.append(index.toString());
		if (scaleVal > 1) buf.append(',' + Integer.toString(scaleVal));

		if( (base != null) || (index != null) || (scaleVal > 1) )
			buf.append(')');

		return buf.toString();
	}
}
