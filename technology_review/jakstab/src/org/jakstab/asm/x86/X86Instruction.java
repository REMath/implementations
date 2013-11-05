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

package org.jakstab.asm.x86;

import org.jakstab.asm.*;

public class X86Instruction extends AbstractInstruction
implements Instruction, X86Opcodes, MemoryInstruction {

	final private int size;
	final private int prefixes;
	final private DataType dataType; //RTL dataType
	final private Operand[] operands;
	final private int operandCount;
	private String description;

	public String getPrefixString() {
		StringBuffer buf = new StringBuffer();
		if ((prefixes & PREFIX_REPZ) != 0)
			buf.append("repz ");
		if ((prefixes & PREFIX_REPNZ) != 0)
			buf.append("repnz ");
		if ((prefixes & PREFIX_LOCK) != 0)
			buf.append("lock ");
		return buf.toString();
	}
	
	public boolean hasPrefixREPZ() {
		return (prefixes & PREFIX_REPZ) != 0;
	}

	public boolean hasPrefixREPNZ() {
		return (prefixes & PREFIX_REPNZ) != 0;
	}

	public boolean hasPrefixLOCK() {
		return (prefixes & PREFIX_LOCK) != 0;
	}

	public int getSize() {
		return size;
	}

	public String toString(long currentPc, SymbolFinder symFinder) {
		if (description == null) 
			description = initDescription(currentPc, symFinder);
		return description;
	}

	@Override
	public int getOperandCount() {
		return operandCount;
	}

	@Override
	public Operand getOperand(int i) {
		return operands[i];
	}

	public Operand getOperand1() {
		return operands[0];
	}

	public Operand getOperand2() {
		return operands[1];
	}

	public Operand getOperand3() {
		return operands[2];
	}

	public DataType getDataType() {
		return dataType;
	}
	
	public boolean hasEsiBasedMemorySource() {
		return (getOperand2() instanceof X86MemoryOperand &&
				((X86MemoryOperand)getOperand2()).getBase().equals(X86Registers.ESI));
	}

	public boolean hasEdiBasedMemoryTarget() {
		return (getOperand1() instanceof X86MemoryOperand &&
				((X86MemoryOperand)getOperand1()).getBase().equals(X86Registers.EDI));
	}

	public X86Instruction(String name, Operand op1, Operand op2, Operand op3, DataType dataType, int size, int prefixes) {
		super(name);
		this.size = size;
		this.prefixes = prefixes;
		this.operands = new Operand[]{op1, op2, op3};
		// Count non-null operands
		int operandCount = 3;
		for (int i=0; i < operands.length; i++) {
			if (operands[i] == null) {
				operandCount = i;
				break;
			}
		}
		this.operandCount = operandCount;
		this.dataType = dataType;
		// initialized when needed for the first time
		description = null;
	}

	public X86Instruction(String name, Operand op1, Operand op2, Operand op3, int size, int prefixes) {
		this(name, op1, op2, op3, DataType.UNKNOWN, size, prefixes);
	}

	public X86Instruction(String name, Operand op1, Operand op2, DataType dataType, int size, int prefixes) {
		this(name, op1, op2, (Operand)null, dataType, size, prefixes);
	}

	public X86Instruction(String name, Operand op1, Operand op2, int size, int prefixes) {
		this(name, op1, op2, (Operand)null, size, prefixes);
	}

	public X86Instruction(String name, Operand op1, int size, int prefixes) {
		this(name, op1, (Operand)null, (Operand)null, size, prefixes);
	}

	public X86Instruction(String name, int size, int prefixes) {
		this(name, (Operand)null, (Operand)null, (Operand)null, size, prefixes);
	}

	protected String initDescription(long currentPc, SymbolFinder symFinder) {
		StringBuffer buf = new StringBuffer();
		buf.append(getPrefixString());
		buf.append(getName());

		buf.append(spaces);
		if (operands[2] != null) {
			//buf.append("(");
			//buf.append(operands[2].getClass().getSimpleName());
			//buf.append(")");
			buf.append(operands[2].toString(currentPc, symFinder));
			buf.append(comma);
		}
		if (operands[1] != null) {
			//buf.append("(");
			//buf.append(operands[1].getClass().getSimpleName());
			//buf.append(")");
			buf.append(operands[1].toString(currentPc, symFinder));
			buf.append(comma);
		}
		if(operands[0] != null) {
			//buf.append("(");
			//buf.append(operands[0].getClass().getSimpleName());
			//buf.append(")");
			buf.append(operands[0].toString(currentPc, symFinder));
		}
		return buf.toString();
	}

	protected static String comma = ", ";
	protected static String spaces = "\t";

}
