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

import org.jakstab.asm.PCRelativeAddress;

//address is specified as an offset from current PC

public class X86PCRelativeAddress extends PCRelativeAddress {
	private int instrSize;

	public X86PCRelativeAddress(long disp) {
		super(disp);
	}

	public void setInstructionSize(int size) {
		instrSize = size;
	}

	/*
	 * @see org.jakstab.asm.PCRelativeAddress#getEffectiveValue(long)
	 */
	@Override
	public long getEffectiveValue(long pcValue) {
		return super.getEffectiveValue(pcValue) + instrSize;
	}

	/**
	 * Returns the displacement as it is encoded in the instruction, that
	 * is, from the start of the next instruction. To get the displacement
	 * from the start of the current instruction, one needs to add the instruction
	 * size.
	 * 
	 * @return the target's displacement from the start of the next instruction.
	 */
	public long getDisplacement() {
		long displacement = super.getDisplacement();
		return displacement;
	}
}
