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

public class X86MMXRegisters {

	private final static Logger logger = Logger.getLogger(X86MMXRegisters.class);

	public static final int NUM_MMX_REGISTERS = 8;

	public static final X86MMXRegister MM0;
	public static final X86MMXRegister MM1;
	public static final X86MMXRegister MM2;
	public static final X86MMXRegister MM3;
	public static final X86MMXRegister MM4;
	public static final X86MMXRegister MM5;
	public static final X86MMXRegister MM6;
	public static final X86MMXRegister MM7;

	private static X86MMXRegister mmxRegisters[];

	static {
		MM0 = new X86MMXRegister(0, "%mm0");
		MM1 = new X86MMXRegister(1, "%mm1");
		MM2 = new X86MMXRegister(2, "%mm2");
		MM3 = new X86MMXRegister(3, "%mm3");
		MM4 = new X86MMXRegister(4, "%mm4");
		MM5 = new X86MMXRegister(5, "%mm5");
		MM6 = new X86MMXRegister(6, "%mm6");
		MM7 = new X86MMXRegister(7, "%mm7");

		mmxRegisters = (new X86MMXRegister[] {
				MM0, MM1, MM2, MM3, MM4, MM5, MM6, MM7
		});
	}

	public static int getNumberOfRegisters() {
		return NUM_MMX_REGISTERS;
	}

	public static String getRegisterName(int regNum) {
		if (regNum < 0 || regNum >= NUM_MMX_REGISTERS) {
			logger.error("Invalid MMX register number!");
			return null;
		}
		return mmxRegisters[regNum].toString();
	}

	public static X86MMXRegister getRegister(int regNum) {
		if (regNum < 0 || regNum >= NUM_MMX_REGISTERS) {
			logger.error("Invalid MMX register number!");
			return null;
		}
		return mmxRegisters[regNum];
	}
}
