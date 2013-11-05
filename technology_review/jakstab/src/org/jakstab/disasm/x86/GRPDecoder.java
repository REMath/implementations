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

public class GRPDecoder extends InstructionDecoder {

   final private int number;
   //Please refer to IA-32 Intel Architecture Software Developer's Manual Volume 2
   //APPENDIX A - Table A-4. Opcode Extensions for One and Two-byte Opcodes by Group Number.
   private static final InstructionDecoder grpTable[][] = {
      {
      new ArithmeticDecoder("addb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.ADD),
      new ArithmeticDecoder("orb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.OR),
      new ArithmeticDecoder("adcb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.ADDC),
      new ArithmeticDecoder("sbbb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.SUBC),
      new ArithmeticDecoder("andb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.AND),
      new ArithmeticDecoder("subb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.SUB),
      new ArithmeticDecoder("xorb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.XOR),
      new InstructionDecoder("cmpb", ADDR_E, b_mode, ADDR_I, b_mode)
      },
      {
      new ArithmeticDecoder("addS", ADDR_E, v_mode, ADDR_I, v_mode, Operation.ADD),
      new ArithmeticDecoder("orS", ADDR_E, v_mode, ADDR_I, v_mode, Operation.OR),
      new ArithmeticDecoder("adcS", ADDR_E, v_mode, ADDR_I, v_mode, Operation.ADDC),
      new ArithmeticDecoder("sbbS", ADDR_E, v_mode, ADDR_I, v_mode, Operation.SUBC),
      new ArithmeticDecoder("andS", ADDR_E, v_mode, ADDR_I, v_mode, Operation.AND),
      new ArithmeticDecoder("subS", ADDR_E, v_mode, ADDR_I, v_mode, Operation.SUB),
      new ArithmeticDecoder("xorS", ADDR_E, v_mode, ADDR_I, v_mode, Operation.XOR),
      new InstructionDecoder("cmpS", ADDR_E, v_mode, ADDR_I, v_mode)
      },
      {
      new ArithmeticDecoder("addS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.ADD), /*note: sIb here*/
      new ArithmeticDecoder("orS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.OR),
      new ArithmeticDecoder("adcS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.ADDC),
      new ArithmeticDecoder("sbbS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.SUBC),
      new ArithmeticDecoder("andS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.AND),
      new ArithmeticDecoder("subS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.SUB),
      new ArithmeticDecoder("xorS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.XOR),
      new InstructionDecoder("cmpS", ADDR_E, v_mode, ADDR_I, b_mode)
      },
      {
      new ArithmeticDecoder("rolb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.RL),
      new ArithmeticDecoder("rorb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.RR),
      new ArithmeticDecoder("rclb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.RLC),
      new ArithmeticDecoder("rcrb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.RRC),
      new ArithmeticDecoder("shlb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.SLL),
      new ArithmeticDecoder("shrb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.SRL),
      null,
      new ArithmeticDecoder("sarb", ADDR_E, b_mode, ADDR_I, b_mode, Operation.SRA),
      },
      {
      new ArithmeticDecoder("rolS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.RL),
      new ArithmeticDecoder("rorS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.RR),
      new ArithmeticDecoder("rclS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.RLC),
      new ArithmeticDecoder("rcrS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.RRC),
      new ArithmeticDecoder("shlS", ADDR_E, v_mode, ADDR_I, b_mode,  Operation.SLL),
      new ArithmeticDecoder("shrS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.SRL),
      null,
      new ArithmeticDecoder("sarS", ADDR_E, v_mode, ADDR_I, b_mode, Operation.SRA)
      },
      {
      new ArithmeticDecoder("rolb", ADDR_E, b_mode, Operation.RL),
      new ArithmeticDecoder("rorb", ADDR_E, b_mode, Operation.RR),
      new ArithmeticDecoder("rclb", ADDR_E, b_mode, Operation.RLC),
      new ArithmeticDecoder("rcrb", ADDR_E, b_mode, Operation.RRC),
      new ArithmeticDecoder("shlb", ADDR_E, b_mode, Operation.SLL),
      new ArithmeticDecoder("shrb", ADDR_E, b_mode, Operation.SRL),
      null,
      new ArithmeticDecoder("sarb", ADDR_E, b_mode, Operation.SRA)
      },
      {
      new ArithmeticDecoder("rolS", ADDR_E, v_mode, Operation.RL),
      new ArithmeticDecoder("rorS", ADDR_E, v_mode, Operation.RR),
      new ArithmeticDecoder("rclS", ADDR_E, v_mode, Operation.RLC),
      new ArithmeticDecoder("rcrS", ADDR_E, v_mode, Operation.RRC),
      new ArithmeticDecoder("shlS", ADDR_E, v_mode, Operation.SLL),
      new ArithmeticDecoder("shrS", ADDR_E, v_mode, Operation.SRL),
      null,
      new ArithmeticDecoder("sarS", ADDR_E, v_mode, Operation.SRA)
      },
      {
      new ArithmeticDecoder("rolb", ADDR_E, b_mode, ADDR_REG, CL, Operation.RL),
      new ArithmeticDecoder("rorb", ADDR_E, b_mode, ADDR_REG, CL, Operation.RR),
      new ArithmeticDecoder("rclb", ADDR_E, b_mode, ADDR_REG, CL, Operation.RLC),
      new ArithmeticDecoder("rcrb", ADDR_E, b_mode, ADDR_REG, CL, Operation.RRC),
      new ArithmeticDecoder("shlb", ADDR_E, b_mode, ADDR_REG, CL, Operation.SLL),
      new ArithmeticDecoder("shrb", ADDR_E, b_mode, ADDR_REG, CL, Operation.SRL),
      null,
      new ArithmeticDecoder("sarb", ADDR_E, b_mode, ADDR_REG, CL, Operation.SRA)
      },
      {
      new ArithmeticDecoder("rolS", ADDR_E, v_mode, ADDR_REG, CL, Operation.RL),
      new ArithmeticDecoder("rorS", ADDR_E, v_mode, ADDR_REG, CL, Operation.RR),
      new ArithmeticDecoder("rclS", ADDR_E, v_mode, ADDR_REG, CL, Operation.RLC),
      new ArithmeticDecoder("rcrS", ADDR_E, v_mode, ADDR_REG, CL, Operation.RRC),
      new ArithmeticDecoder("shlS", ADDR_E, v_mode, ADDR_REG, CL, Operation.SLL),
      new ArithmeticDecoder("shrS", ADDR_E, v_mode, ADDR_REG, CL, Operation.SRL),
      null,
      new ArithmeticDecoder("sarS", ADDR_E, v_mode, ADDR_REG, CL, Operation.SRA)
      },
      {
      new InstructionDecoder("testb", ADDR_E, b_mode, ADDR_I, b_mode),
      null, /*new InstructionDecoder("(bad)", ADDR_E, b_mode)*/
      new ArithmeticDecoder("notb", ADDR_E, b_mode, Operation.NOT),
      new InstructionDecoder("negb", ADDR_E, b_mode),
      new ArithmeticDecoder("mulb", ADDR_REG, AL, ADDR_E, b_mode, Operation.UMUL),
      new ArithmeticDecoder("imulb", ADDR_REG, AL, ADDR_E, b_mode, Operation.SMUL),
      new ArithmeticDecoder("divb", ADDR_REG, AL, ADDR_E, b_mode, Operation.UDIV),
      new ArithmeticDecoder("idivb", ADDR_REG, AL, ADDR_E, b_mode, Operation.SDIV)
      },
      {
      new InstructionDecoder("testS", ADDR_E, v_mode, ADDR_I, v_mode),
      null,
      new ArithmeticDecoder("notS", ADDR_E, v_mode, Operation.NOT),
      new InstructionDecoder("negS", ADDR_E, v_mode),
      new ArithmeticDecoder("mulS", ADDR_REG, EAX, ADDR_E, v_mode, Operation.UMUL),
      new ArithmeticDecoder("imulS", ADDR_REG, EAX, ADDR_E, v_mode, Operation.SMUL),
      new ArithmeticDecoder("divS", ADDR_REG, EAX, ADDR_E, v_mode, Operation.SDIV),
      new ArithmeticDecoder("idivS", ADDR_REG, EAX, ADDR_E, v_mode, Operation.SDIV)
      },
      {
      new ArithmeticDecoder("incb", ADDR_E, b_mode, Operation.ADD),
      new ArithmeticDecoder("decb", ADDR_E, b_mode, Operation.SUB),
      null,
      null,
      null,
      null,
      null,
      null
      },
      {
      new ArithmeticDecoder("incS", ADDR_E, v_mode, Operation.ADD),
      new ArithmeticDecoder("decS", ADDR_E, v_mode, Operation.SUB),
      new CallDecoder("call", ADDR_E, v_mode),
      new CallDecoder("lcall", ADDR_E, p_mode),
      new JmpDecoder("jmp", ADDR_E, v_mode),
      new JmpDecoder("ljmp", ADDR_E, p_mode),
      new InstructionDecoder("pushS", ADDR_E, v_mode),
      null
      },
      {
      new InstructionDecoder("sldt", ADDR_E, w_mode),
      new InstructionDecoder("str", ADDR_E, w_mode),
      new InstructionDecoder("lldt", ADDR_E, w_mode),
      new InstructionDecoder("ltr", ADDR_E, w_mode),
      new InstructionDecoder("verr", ADDR_E, w_mode),
      new InstructionDecoder("verw", ADDR_E, w_mode),
      null,
      null
      },
      {
      new InstructionDecoder("sgdt", ADDR_E, w_mode),
      new InstructionDecoder("sidt", ADDR_E, w_mode),
      new InstructionDecoder("lgdt", ADDR_E, w_mode),
      new InstructionDecoder("lidt", ADDR_E, w_mode),
      new InstructionDecoder("smsw", ADDR_E, w_mode),
      null,
      new InstructionDecoder("lmsw", ADDR_E, w_mode),
      new InstructionDecoder("invlpg", ADDR_E, w_mode)
      },
      {
      null,
      null,
      null,
      null,
      new InstructionDecoder("btS", ADDR_E, v_mode, ADDR_I, b_mode),
      new InstructionDecoder("btsS", ADDR_E, v_mode, ADDR_I, b_mode),
      new InstructionDecoder("btrS", ADDR_E, v_mode, ADDR_I, b_mode),
      new InstructionDecoder("btcS", ADDR_E, v_mode, ADDR_I, b_mode)
      },
      /*16*/
      {
      null,
      new SSEInstructionDecoder("cmpxch8b", ADDR_W, q_mode),
      null,
      null,
      null,
      null,
      null,
      null
      },
      /*17*/
      {
      null,
      null,
      new SSEArithmeticDecoder("psrlw", ADDR_P, q_mode, ADDR_I, b_mode, Operation.SRL),
      null,
      new SSEArithmeticDecoder("psraw", ADDR_P, q_mode, ADDR_I, b_mode, Operation.SRA),
      null,
      new SSEArithmeticDecoder("psllw", ADDR_P, q_mode, ADDR_I, b_mode, Operation.SLL),
      null
      },
      /*18*/
      {
      null,
      null,
      new SSEArithmeticDecoder("psrld", ADDR_P, q_mode, ADDR_I, b_mode, Operation.SRL),
      null,
      new SSEArithmeticDecoder("psrad", ADDR_P, q_mode, ADDR_I, b_mode, Operation.SRA),
      null,
      new SSEArithmeticDecoder("pslld", ADDR_P, q_mode, ADDR_I, b_mode, Operation.SLL),
      null
      },
      /*19*/
      {
      null,
      null,
      new SSEArithmeticDecoder("psrlq", ADDR_P, q_mode, ADDR_I, b_mode, Operation.SRL),
      null,
      null,
      null,
      new SSEArithmeticDecoder("psllq", ADDR_P, q_mode, ADDR_I, b_mode, Operation.SLL),
      null
      },
      /*20 - Grp15*/
      {
    	  // FIXME: JK: I think these are wrong - byteindex is not advanced by constructor
    	  // without operands, even though a modrm byte is present!
      new SSEInstructionDecoder("fxsave", ADDR_E, b_mode),
      new SSEInstructionDecoder("fxrstor", ADDR_E, b_mode),
      new SSEInstructionDecoder("ldmxcsr", ADDR_E, d_mode),
      new SSEInstructionDecoder("stmxcsr", ADDR_E, d_mode),
      null,
      null,
      null,
      new SSEInstructionDecoder("clflush", ADDR_E, b_mode)
      },
      /*21 - Grp16*/
      {
      new SSEInstructionDecoder("prefetchnta", ADDR_E, b_mode),
      new SSEInstructionDecoder("prefetcht0", ADDR_E, b_mode),
      new SSEInstructionDecoder("prefetcht1", ADDR_E, b_mode),
      new SSEInstructionDecoder("prefetcht2", ADDR_E, b_mode),
      null,
      null,
      null,
      null
      },
      /*22 - Grp12:66*/
      {
      null,
      null,
      new SSEArithmeticDecoder("psrlw", ADDR_P, dq_mode, ADDR_I, b_mode, Operation.SRL),
      null,
      new SSEArithmeticDecoder("psraw", ADDR_P, dq_mode, ADDR_I, b_mode, Operation.SRA),
      null,
      new SSEArithmeticDecoder("psllw", ADDR_P, dq_mode, ADDR_I, b_mode, Operation.SLL),
      null
      },
      /*23 - Grp13:66*/
      {
      null,
      null,
      new SSEArithmeticDecoder("psrld", ADDR_W, dq_mode, ADDR_I, b_mode, Operation.SRL),
      null,
      new SSEArithmeticDecoder("psrad", ADDR_W, dq_mode, ADDR_I, b_mode, Operation.SRA),
      null,
      new SSEArithmeticDecoder("pslld", ADDR_W, dq_mode, ADDR_I, b_mode, Operation.SLL),
      null
      },
      /*24 - - Grp14:66*/
      {
      null,
      null,
      new SSEArithmeticDecoder("psrlq", ADDR_W, dq_mode, ADDR_I, b_mode, Operation.SRL),
      new SSEArithmeticDecoder("psrldq", ADDR_W, dq_mode, ADDR_I, b_mode, Operation.SRL),
      null,
      null,
      new SSEArithmeticDecoder("psllq", ADDR_W, dq_mode, ADDR_I, b_mode, Operation.SLL),
      new SSEArithmeticDecoder("psllq", ADDR_W, dq_mode, ADDR_I, b_mode, Operation.SLL)
      }
};

   public GRPDecoder(String name, int number) {
      super(name);
      this.number = number;
   }

   public Instruction decode(BinaryInputBuffer bytesArray, int index, int instrStartIndex, int segmentOverride, int prefixes, X86InstructionFactory factory) {
      this.byteIndex = index;
      this.instrStartIndex = instrStartIndex;
      this.prefixes = prefixes;

      int ModRM = readByte(bytesArray, byteIndex);
      int reg = (ModRM >> 3) & 7;

      InstructionDecoder instrDecoder = grpTable[number][reg];
      Instruction instr = null;
      if(instrDecoder != null) {
         instr = instrDecoder.decode(bytesArray, byteIndex, instrStartIndex, segmentOverride, prefixes, factory);
         byteIndex = instrDecoder.getCurrentIndex();
      }
      return instr;
   }
}
