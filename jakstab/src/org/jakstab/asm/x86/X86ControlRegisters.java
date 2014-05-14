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

import org.jakstab.util.Logger;

/**
 * The control registers CR0, CR2, CR3, and CR4 on IA32. 
 * @author Johannes Kinder
 */
public class X86ControlRegisters {
	
	private final static Logger logger = Logger.getLogger(X86ControlRegisters.class);

	public static final int NUM_CONTROL_REGISTERS = 5;

	public static final X86ControlRegister INVALID; //Invalid dummy

	public static final X86ControlRegister CR0;
	public static final X86ControlRegister CR2;
	public static final X86ControlRegister CR3;
	public static final X86ControlRegister CR4;

	private static X86ControlRegister controlRegisters[];

	static {
		CR0 = new X86ControlRegister(0, "%cr0");
		INVALID = new X86ControlRegister(1, "Invalid Control Register");
		CR2 = new X86ControlRegister(2, "%cr2");
		CR3 = new X86ControlRegister(3, "%cr3");
		CR4 = new X86ControlRegister(4, "%cr4");

		controlRegisters = (new X86ControlRegister[] {
				CR0, INVALID, CR2, CR3, CR4
		});
	}

	public static int getNumberOfRegisters() {
		return NUM_CONTROL_REGISTERS;
	}

	public static String getRegisterName(int regNum) {
		if (regNum < 0 || regNum >= NUM_CONTROL_REGISTERS) {
			logger.error("Invalid control register number!");
			return null;
		}
		return controlRegisters[regNum].toString();
	}

	public static X86ControlRegister getRegister(int regNum) {
		if (regNum < 0 || regNum >= NUM_CONTROL_REGISTERS) {
			logger.error("Invalid control register number!");
			return null;
		}
		return controlRegisters[regNum];
	}
}
