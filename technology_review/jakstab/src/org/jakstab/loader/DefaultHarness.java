/*
 * DefaultHarness.java - This file is part of the Jakstab project.
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
package org.jakstab.loader;

import org.jakstab.Program;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class DefaultHarness implements Harness {
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(DefaultHarness.class);

	public static long PROLOGUE_BASE = 0xface0000L;
	public static long EPILOGUE_BASE = 0xfee70000L;
	private AbsoluteAddress prologueAddress = new AbsoluteAddress(PROLOGUE_BASE);
	private AbsoluteAddress epilogueAddress = new AbsoluteAddress(EPILOGUE_BASE);

	private RTLVariable esp = Program.getProgram().getArchitecture().stackPointer(); 
	
	@Override
	public void install(Program program) {

		StatementSequence seq = new StatementSequence();
		seq.addLast(new RTLVariableAssignment(1, ExpressionFactory.createVariable("%DF", 1), ExpressionFactory.FALSE));
		seq.addLast(new RTLAlloc(esp, MemoryRegion.STACK.toString()));
		
		// Allocate TLS depending on OS type
		if (program.getTargetOS() == Program.TargetOS.WINDOWS)
			seq.addLast(new RTLAlloc(ExpressionFactory.createVariable("%fs", 16), "FS"));
		else if (program.getTargetOS() == Program.TargetOS.LINUX)
			seq.addLast(new RTLAlloc(ExpressionFactory.createVariable("%gs", 16), "GS"));
		
		// Pseudo-stackframe for in-procedure entry points during debugging
		//seq.addLast(new RTLVariableAssignment(32, program.getArchitecture().framePointer(), program.getArchitecture().stackPointer()));
		//seq.addLast(new RTLVariableAssignment(32, ExpressionFactory.createVariable("%ebx"), program.getArchitecture().stackPointer()));

		push32(seq, ExpressionFactory.createNumber(epilogueAddress.getValue(), 32));
		seq.addLast(new RTLGoto(ExpressionFactory.createNumber(program.getStart().getAddress().getValue(), 32), RTLGoto.Type.CALL));
		putSequence(program, seq, prologueAddress);
		
		program.setEntryAddress(prologueAddress);

		// epilogue with halt statement
		seq = new StatementSequence();
		//seq.addLast(new RTLSkip());
		seq.addLast(new RTLHalt());
		putSequence(program, seq, epilogueAddress);
	}
	
	private void push32(StatementSequence seq, RTLExpression value) {
		seq.addLast(new RTLVariableAssignment(esp.getBitWidth(), esp, 
				ExpressionFactory.createPlus(esp, ExpressionFactory.createNumber(-4, esp.getBitWidth()))
		));
		if (value != null) {
			seq.addLast(new RTLMemoryAssignment(ExpressionFactory.createMemoryLocation(esp, 32), value));
		}
	}
	
	private void putSequence(Program program, StatementSequence seq, AbsoluteAddress address) {
		int rtlId = 0;
		for (RTLStatement stmt : seq) {
			stmt.setLabel(address, rtlId++);
			stmt.setNextLabel(new Location(address, rtlId));
		}
		seq.getLast().setNextLabel(null);

		// add stub statements to program
		for (RTLStatement s : seq)
			program.putStatement(s);
	}

	@Override
	public boolean contains(AbsoluteAddress a) {
		return (a.equals(prologueAddress) || a.equals(epilogueAddress));
	}

	@Override
	public AbsoluteAddress getFallthroughAddress(AbsoluteAddress a) {
		if (a.equals(prologueAddress))
			return epilogueAddress;
		else
			return null;
	}

}
