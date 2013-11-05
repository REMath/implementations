/*
 * MagicInstructions.java - This file is part of the Jakstab project.
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
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
 * 2 along with this work; if not, see <http://www.gnu.org/licenses/>.
 */
package org.jakstab.ssl;

import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.expressions.Writable;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class MagicInstructions {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(MagicInstructions.class);
	
	private final SSLInstruction allocPrototype; 
	private final SSLInstruction deallocPrototype; 
	private final SSLInstruction nondet8Prototype; 
	private final SSLInstruction nondet16Prototype; 
	private final SSLInstruction nondet32Prototype;
	private final SSLInstruction havoc8leqPrototype;
	private final SSLInstruction havoc16leqPrototype;
	private final SSLInstruction havoc32leqPrototype;
	private final SSLInstruction assertGTPrototype;
	private final SSLInstruction assertGEPrototype;
	private final SSLInstruction assertEQPrototype;
	
	protected MagicInstructions() {
		RTLVariable reg8 = ExpressionFactory.createVariable("reg8"); 
		RTLVariable reg16 = ExpressionFactory.createVariable("reg16"); 
		RTLVariable reg32 = ExpressionFactory.createVariable("reg32");
		RTLVariable i8 = ExpressionFactory.createVariable("i8");
		RTLVariable i16 = ExpressionFactory.createVariable("i16");
		RTLVariable i32 = ExpressionFactory.createVariable("i32");
		Writable modrm = ExpressionFactory.createVariable("modrm");
		allocPrototype = makePrototype(
				"ALLOC", 
				new RTLAlloc(reg32),
				reg32.toString()
				);
		deallocPrototype = makePrototype(
				"DEALLOC", 
				new RTLDealloc(ExpressionFactory.createVariable("modrm")),
				modrm.toString()
				);
		nondet8Prototype = makePrototype(
				"NONDET8", 
				new AssignmentTemplate(8, reg8, ExpressionFactory.nondet(8)),
				reg8.toString(),
				i8.toString()
				);
		nondet16Prototype = makePrototype(
				"NONDET16", 
				new AssignmentTemplate(16, reg16, ExpressionFactory.nondet(16)),
				reg16.toString(),
				i16.toString()
				);
		nondet32Prototype = makePrototype(
				"NONDET32", 
				new AssignmentTemplate(32, reg32, ExpressionFactory.nondet(32)),
				reg32.toString(),
				i32.toString()
				);
		havoc8leqPrototype = makePrototype(
				"HAVOC8ULEQ", 
				new RTLHavoc(reg8, i8),
				reg8.toString(),
				i8.toString()
				);
		havoc16leqPrototype = makePrototype(
				"HAVOC16ULEQ", 
				new RTLHavoc(reg16, i16),
				reg16.toString(),
				i16.toString()
				);
		havoc32leqPrototype = makePrototype(
				"HAVOC32ULEQ", 
				new RTLHavoc(reg32, i32),
				reg32.toString(),
				i32.toString()
				);
		assertGTPrototype = makePrototype(
				"ASSERTGT", 
				new RTLAssert(ExpressionFactory.createGreaterThan(
						reg32, ExpressionFactory.createCast(modrm, ExpressionFactory.createNumber(32, 8)))),
				reg32.toString(),
				modrm.toString()
				);
		assertGEPrototype = makePrototype(
				"ASSERTGE", 
				new RTLAssert(ExpressionFactory.createGreaterOrEqual(
						reg32, ExpressionFactory.createCast(modrm, ExpressionFactory.createNumber(32, 8)))),
				reg32.toString(),
				modrm.toString()
				);
		assertEQPrototype = makePrototype(
				"ASSERTEQ", 
				new RTLAssert(ExpressionFactory.createEqual(
						reg32, ExpressionFactory.createCast(modrm, ExpressionFactory.createNumber(32, 8)))),
				reg32.toString(),
				modrm.toString()
				);
	}
	
	private SSLInstruction makePrototype(String name, RTLStatement statement, String... params) {
		StatementSequence seq = new StatementSequence();
		seq.addFirst(statement);
		return new SSLInstruction(name, params, seq);
	}

	public SSLInstruction getAllocPrototype() {
		return allocPrototype;
	}

	public SSLInstruction getDeallocPrototype() {
		return deallocPrototype;
	}

	public SSLInstruction getNondet8Prototype() {
		return nondet8Prototype;
	}

	public SSLInstruction getNondet16Prototype() {
		return nondet16Prototype;
	}

	public SSLInstruction getNondet32Prototype() {
		return nondet32Prototype;
	}
	
	public SSLInstruction getHavoc8Prototype() {
		return havoc8leqPrototype;
	}

	public SSLInstruction getHavoc16Prototype() {
		return havoc16leqPrototype;
	}

	public SSLInstruction getHavoc32Prototype() {
		return havoc32leqPrototype;
	}

	public SSLInstruction getAssertGTPrototype() {
		return assertGTPrototype;
	}

	public SSLInstruction getAssertGEPrototype() {
		return assertGEPrototype;
	}

	public SSLInstruction getAssertEQPrototype() {
		return assertEQPrototype;
	}
	
}
