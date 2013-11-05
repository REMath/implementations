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

public class X86SegmentRegisters {

	private final static Logger logger = Logger.getLogger(X86SegmentRegisters.class);

	public static final int NUM_SEGMENT_REGISTERS = 6;

	public static final X86SegmentRegister ES;
	public static final X86SegmentRegister CS;
	public static final X86SegmentRegister SS;
	public static final X86SegmentRegister DS;
	public static final X86SegmentRegister FS;
	public static final X86SegmentRegister GS;

	private static X86SegmentRegister segmentRegisters[];

	static {
		//Segment registers
		ES = new X86SegmentRegister(0, "%es");
		CS = new X86SegmentRegister(1, "%cs");
		SS = new X86SegmentRegister(2, "%ss");
		DS = new X86SegmentRegister(3, "%ds");
		FS = new X86SegmentRegister(4, "%fs");
		GS = new X86SegmentRegister(5, "%gs");

		segmentRegisters = (new X86SegmentRegister[] {
				ES, CS, SS, DS, FS, GS
		});
	}

	public static int getNumberOfRegisters() {
		return NUM_SEGMENT_REGISTERS;
	}

	public static X86SegmentRegister getSegmentRegister(int regNum) {
		if (regNum < 0 || regNum >= NUM_SEGMENT_REGISTERS) {
			logger.error("Invalid segment register number!");
			return null;
		}
		return segmentRegisters[regNum];
	}
}
