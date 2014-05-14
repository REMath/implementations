/*
 * Copyright 2001 Sun Microsystems, Inc.  All Rights Reserved.
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

public class X86Registers {

	private final static Logger logger = Logger.getLogger(X86Registers.class);

	public static final int NUM_REGISTERS = 8;

	public static final X86Register EAX;
	public static final X86Register ECX;
	public static final X86Register EDX;
	public static final X86Register EBX;
	public static final X86Register ESP;
	public static final X86Register EBP;
	public static final X86Register ESI;
	public static final X86Register EDI;

	public static final X86Register AX;
	public static final X86Register CX;
	public static final X86Register DX;
	public static final X86Register BX;
	public static final X86Register SP;
	public static final X86Register BP;
	public static final X86Register SI;
	public static final X86Register DI;

	public static final X86Register AL;
	public static final X86Register CL;
	public static final X86Register DL;
	public static final X86Register BL;
	public static final X86Register AH;
	public static final X86Register CH;
	public static final X86Register DH;
	public static final X86Register BH;

	private static X86Register registers8[];
	private static X86Register registers16[];
	private static X86Register registers32[];

	static {
		EAX = new X86Register(0, "%eax");
		ECX = new X86Register(1, "%ecx");
		EDX = new X86Register(2, "%edx");
		EBX = new X86Register(3, "%ebx");
		ESP = new X86Register(4, "%esp");
		EBP = new X86Register(5, "%ebp");
		ESI = new X86Register(6, "%esi");
		EDI = new X86Register(7, "%edi");

		AX = new X86RegisterPart(0, "%ax", 0, 16);
		CX = new X86RegisterPart(1, "%cx", 0, 16);
		DX = new X86RegisterPart(2, "%dx", 0, 16);
		BX = new X86RegisterPart(3, "%bx", 0, 16);
		SP = new X86RegisterPart(4, "%sp", 0, 16);
		BP = new X86RegisterPart(5, "%bp", 0, 16);
		SI = new X86RegisterPart(6, "%si", 0, 16);
		DI = new X86RegisterPart(7, "%di", 0, 16);

		AL = new X86RegisterPart(0, "%al", 0, 8);
		CL = new X86RegisterPart(1, "%cl", 0, 8);
		DL = new X86RegisterPart(2, "%dl", 0, 8);
		BL = new X86RegisterPart(3, "%bl", 0, 8);
		AH = new X86RegisterPart(0, "%ah", 8, 8);
		CH = new X86RegisterPart(1, "%ch", 8, 8);
		DH = new X86RegisterPart(2, "%dh", 8, 8);
		BH = new X86RegisterPart(3, "%bh", 8, 8);

		registers32 = (new X86Register[] {
				EAX, ECX, EDX, EBX, ESP, EBP, ESI, EDI
		});
		registers16 = (new X86Register[] {
				AX, CX, DX, BX, SP, BP, SI, DI
		});
		registers8 = (new X86Register[] {
				AL, CL, DL, BL, AH, CH, DH, BH
		});
	}

	public static int getNumberOfRegisters() {
		return NUM_REGISTERS;
	}

	public static X86Register getRegister8(int regNum) {
		if (regNum < 0 || regNum >= NUM_REGISTERS) {
			logger.error("Invalid integer register number!");
			return null;
		}
		return registers8[regNum];
	}

	public static X86Register getRegister16(int regNum) {
		if (regNum < 0 || regNum >= NUM_REGISTERS) {
			logger.error("Invalid integer register number!");
			return null;
		}
		return registers16[regNum];
	}

	public static X86Register getRegister32(int regNum) {
		if (regNum < 0 || regNum >= NUM_REGISTERS) {
			logger.error("Invalid integer register number!");
			return null;
		}
		return registers32[regNum];
	}

	/**
	 * Returns the name of the 32bit register with the given code number.
	 */
	public static String getRegisterName(int regNum) {
		if (regNum < 0 || regNum >= NUM_REGISTERS) {
			logger.error("Invalid integer register number!");
			return null;
		}
		return registers32[regNum].toString();
	}
}
