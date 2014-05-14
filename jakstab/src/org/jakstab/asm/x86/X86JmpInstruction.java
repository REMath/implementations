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

import org.jakstab.asm.*;

public class X86JmpInstruction extends X86Instruction
implements BranchInstruction {

	public X86JmpInstruction(String name, Operand target, int size, int prefixes) {
		super(name, target, size, prefixes);
		if(target instanceof X86PCRelativeAddress) {
			((X86PCRelativeAddress)target).setInstructionSize(getSize());
		}
	}

	@Override
	public Operand getBranchDestination() {
		return getOperand1();
	}

	@Override
	public boolean isConditional() {
		return false;
	}

	@Override
	public boolean isIndirect() {
		return !(getBranchDestination() instanceof PCRelativeAddress || 
				getBranchDestination() instanceof AbsoluteAddress);
	}

	@Override
	public boolean isLeaf() {
		return true;
	}

}
