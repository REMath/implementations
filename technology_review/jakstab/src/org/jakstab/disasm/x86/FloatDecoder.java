/*
 * Copyright 2002-2003 Sun Microsystems, Inc.  All Rights Reserved.
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

package org.jakstab.disasm.x86;

import org.jakstab.asm.Instruction;
import org.jakstab.asm.Operation;
import org.jakstab.asm.x86.X86InstructionFactory;
import org.jakstab.util.BinaryInputBuffer;

public class FloatDecoder extends FPInstructionDecoder {

	public FloatDecoder() {
		super(null);
	}

	//Please refer to IA-32 Intel Architecture Software Developer's Manual Volume 2
	//APPENDIX A - Escape opcodes

	/*When ModR/M byte is within 00h to BFh*/
	private static final FPInstructionDecoder floatMapOne[][] = {
		/* d8 */
		{
			new FPArithmeticDecoder("fadds", ADDR_E, fs_mode, Operation.ADD),
			new FPArithmeticDecoder("fmuls", ADDR_E, fs_mode, Operation.SMUL),
			new FPInstructionDecoder("fcoms", ADDR_E, fs_mode),
			new FPInstructionDecoder("fcomps", ADDR_E, fs_mode),
			new FPArithmeticDecoder("fsubs", ADDR_E, fs_mode, Operation.SUB),
			new FPArithmeticDecoder("fsubrs", ADDR_E, fs_mode, Operation.SUB),
			new FPArithmeticDecoder("fdivs", ADDR_E, fs_mode, Operation.SDIV),
			new FPArithmeticDecoder("fdivrs", ADDR_E, fs_mode, Operation.SDIV)
		},
		/*  d9 */
		{
			new FPLoadDecoder("flds", ADDR_E, fs_mode),
			null,
			new FPStoreDecoder("fsts", ADDR_E, fs_mode),
			new FPStoreDecoder("fstps", ADDR_E, fs_mode),
			new FPStoreDecoder("fldenv", ADDR_E, v_mode),
			new FPStoreDecoder("fldcw", ADDR_E, w_mode),
			new FPStoreDecoder("fNstenv", ADDR_E, b_mode),
			new FPStoreDecoder("fNstcw", ADDR_E, w_mode)
		},
		/* da */
		{
			new FPArithmeticDecoder("fiaddl", ADDR_E, d_mode, Operation.ADD),
			new FPArithmeticDecoder("fimull", ADDR_E, d_mode, Operation.SMUL),
			new FPInstructionDecoder("ficoml", ADDR_E, d_mode),
			new FPInstructionDecoder("ficompl", ADDR_E, d_mode),
			new FPArithmeticDecoder("fisubl", ADDR_E, d_mode, Operation.SUB),
			new FPArithmeticDecoder("fisubrl", ADDR_E, d_mode, Operation.SUB),
			new FPArithmeticDecoder("fidivl", ADDR_E, d_mode, Operation.SDIV),
			new FPArithmeticDecoder("fidivrl", ADDR_E, d_mode, Operation.SDIV)
		},
		/* db */
		{
			new FPLoadDecoder("fildl", ADDR_E, d_mode),
			null,
			new FPStoreDecoder("fistl", ADDR_E, d_mode),
			new FPStoreDecoder("fistpl", ADDR_E, d_mode),
			null,
			new FPLoadDecoder("fldt", ADDR_E, fe_mode),
			null,
			new FPStoreDecoder("fstpt", ADDR_E, fe_mode)
		},
		/* dc */
		{
			new FPArithmeticDecoder("faddl", ADDR_E, fd_mode, Operation.ADD),
			new FPArithmeticDecoder("fmull", ADDR_E, fd_mode, Operation.SMUL),
			new FPInstructionDecoder("fcoml", ADDR_E, fd_mode),
			new FPInstructionDecoder("fcompl", ADDR_E, fd_mode),
			new FPArithmeticDecoder("fsubl", ADDR_E, fd_mode, Operation.SUB),
			new FPArithmeticDecoder("fsubrl", ADDR_E, fd_mode, Operation.SUB),
			new FPArithmeticDecoder("fdivl", ADDR_E, fd_mode, Operation.SDIV),
			new FPArithmeticDecoder("fdivrl", ADDR_E, fd_mode, Operation.SDIV)
		},
		/* dd */
		{
			new FPLoadDecoder("fldl", ADDR_E, fd_mode),
			null,
			new FPStoreDecoder("fstl", ADDR_E, fd_mode),
			new FPStoreDecoder("fstpl", ADDR_E, fd_mode), 
			new FPStoreDecoder("frstor", ADDR_E, v_mode),
			null,
			new FPStoreDecoder("fNsave", ADDR_E, w_mode),
			new FPStoreDecoder("fNstsw", ADDR_E, w_mode)
		},
		/* de */
		{
			new FPArithmeticDecoder("fiadd", ADDR_E, w_mode, Operation.ADD),
			new FPArithmeticDecoder("fimul", ADDR_E, w_mode, Operation.SMUL),
			new FPInstructionDecoder("ficom", ADDR_E, w_mode),
			new FPInstructionDecoder("ficomp", ADDR_E, w_mode),
			new FPArithmeticDecoder("fisub", ADDR_E, w_mode, Operation.SUB),
			new FPArithmeticDecoder("fisubr", ADDR_E, w_mode, Operation.SUB),
			new FPArithmeticDecoder("fidiv", ADDR_E, w_mode, Operation.SDIV),
			new FPArithmeticDecoder("fidivr", ADDR_E, w_mode, Operation.SDIV)
		},
		/* df */
		{
			new FPLoadDecoder("fild", ADDR_E, w_mode),
			null,
			new FPStoreDecoder("fist", ADDR_E, w_mode),
			new FPStoreDecoder("fistp", ADDR_E, w_mode),
			new FPLoadDecoder("fbld", ADDR_E, v_mode),
			new FPLoadDecoder("fildll", ADDR_E, q_mode),
			new FPStoreDecoder("fbstp", ADDR_E, v_mode),
			new FPStoreDecoder("fistpll", ADDR_E, q_mode)
		}
	};

	/*When ModR/M byte is outside 00h to BFh*/
	private static final FPInstructionDecoder floatMapTwo[][] = {

		/* d8 */
		/*parameter for ADDR_FPREG, 0 means ST(0), 1 means ST at rm value. */
		{
			new FPArithmeticDecoder("fadd", ADDR_FPREG, 0, ADDR_FPREG, 1, Operation.ADD),
			new FPArithmeticDecoder("fmul", ADDR_FPREG, 0, ADDR_FPREG, 1, Operation.SMUL),
			new FPInstructionDecoder("fcom", ADDR_FPREG, 1),
			new FPInstructionDecoder("fcomp", ADDR_FPREG, 1),
			new FPArithmeticDecoder("fsub", ADDR_FPREG, 0, ADDR_FPREG, 1, Operation.SUB),
			new FPArithmeticDecoder("fsubr", ADDR_FPREG, 0, ADDR_FPREG, 1, Operation.SUB),
			new FPArithmeticDecoder("fdiv", ADDR_FPREG, 0, ADDR_FPREG, 1, Operation.SDIV),
			new FPArithmeticDecoder("fdivr", ADDR_FPREG, 0, ADDR_FPREG, 1, Operation.SDIV)
		},
		/* d9 */
		{
			new FPLoadDecoder("fld", ADDR_FPREG, 1),
			new FPInstructionDecoder("fxch", ADDR_FPREG, 1),
			new FloatGRPDecoder(null, 0),
			null,
			new FloatGRPDecoder(null, 1),
			new FloatGRPDecoder(null, 2),
			new FloatGRPDecoder(null, 3),
			new FloatGRPDecoder(null, 4)
		},
		/* da */
		{
			null,
			null,
			null,
			null,
			null,
			new FloatGRPDecoder(null, 5),
			null,
			null
		},
		/* db */
		{
			null,
			null,
			null,
			null,
			new FloatGRPDecoder(null, 6),
			null,
			null,
			null
		},
		/* dc */
		{
			new FPArithmeticDecoder("fadd", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.ADD),
			new FPArithmeticDecoder("fmul", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SMUL),
			null,
			null,
			new FPArithmeticDecoder("fsub", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SUB),
			new FPArithmeticDecoder("fsubr",ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SUB),
			new FPArithmeticDecoder("fdiv", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SDIV),
			new FPArithmeticDecoder("fdivr", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SDIV)
		},
		/* dd */
		{
			new FPInstructionDecoder("ffree", ADDR_FPREG, 1),
			null,
			new FPStoreDecoder("fst", ADDR_FPREG, 1),
			new FPStoreDecoder("fstp", ADDR_FPREG, 1),
			new FPInstructionDecoder("fucom", ADDR_FPREG, 1),
			new FPInstructionDecoder("fucomp", ADDR_FPREG, 1),
			null,
			null
		},
		/* de */
		{
			new FPArithmeticDecoder("faddp", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.ADD),
			new FPArithmeticDecoder("fmulp", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SMUL),
			null,
			new FloatGRPDecoder(null, 7),
			new FPArithmeticDecoder("fsubrp", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SUB),
			new FPArithmeticDecoder("fsubp", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SUB),
			new FPArithmeticDecoder("fdivrp", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SDIV),
			new FPArithmeticDecoder("fdivp", ADDR_FPREG, 1, ADDR_FPREG, 0, Operation.SDIV)
		},
		/* df */
		{
			null,
			null,
			null,
			null,
			new FloatGRPDecoder(null, 8),
			null,
			null,
			null
		}
	};

	public Instruction decode(BinaryInputBuffer bytesArray, int index, int instrStartIndex, int segmentOverride, int prefixes, X86InstructionFactory factory) {
		this.byteIndex = index;
		this.instrStartIndex = instrStartIndex;
		this.prefixes = prefixes;

		int ModRM = readByte(bytesArray, byteIndex);
		int reg = (ModRM >> 3) & 7;
		// int regOrOpcode = (ModRM >> 3) & 7;
		// int rm = ModRM & 7;

		int startIndexWithoutPrefix;
		
		// JK: FWAIT was broken
		if ((prefixes & PREFIX_FWAIT) != 0)
			startIndexWithoutPrefix = instrStartIndex + 1;
		else
			startIndexWithoutPrefix = instrStartIndex;
		
		int floatOpcode = InstructionDecoder.readByte(bytesArray, startIndexWithoutPrefix);

		FPInstructionDecoder instrDecoder = null;

		if(ModRM < 0xbf) {
			instrDecoder = floatMapOne[floatOpcode - 0xd8][reg];
		}
		else {
			instrDecoder = floatMapTwo[floatOpcode - 0xd8][reg];
		}

		Instruction instr = null;
		if(instrDecoder != null) {
			instr = instrDecoder.decode(bytesArray, byteIndex, instrStartIndex, segmentOverride, prefixes, factory);
			byteIndex = instrDecoder.getCurrentIndex();
		}

		return instr;
	}
}
